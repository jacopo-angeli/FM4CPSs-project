import pynusmv
import sys
from pynusmv_lower_interface.nusmv.parser import parser
from collections import deque

specTypes = {
    "LTLSPEC": parser.TOK_LTLSPEC,
    "CONTEXT": parser.CONTEXT,
    "IMPLIES": parser.IMPLIES,
    "IFF": parser.IFF,
    "OR": parser.OR,
    "XOR": parser.XOR,
    "XNOR": parser.XNOR,
    "AND": parser.AND,
    "NOT": parser.NOT,
    "ATOM": parser.ATOM,
    "NUMBER": parser.NUMBER,
    "DOT": parser.DOT,
    "NEXT": parser.OP_NEXT,
    "OP_GLOBAL": parser.OP_GLOBAL,
    "OP_FUTURE": parser.OP_FUTURE,
    "UNTIL": parser.UNTIL,
    "EQUAL": parser.EQUAL,
    "NOTEQUAL": parser.NOTEQUAL,
    "LT": parser.LT,
    "GT": parser.GT,
    "LE": parser.LE,
    "GE": parser.GE,
    "TRUE": parser.TRUEEXP,
    "FALSE": parser.FALSEEXP,
}

basicTypes = {
    parser.ATOM,
    parser.NUMBER,
    parser.TRUEEXP,
    parser.FALSEEXP,
    parser.DOT,
    parser.EQUAL,
    parser.NOTEQUAL,
    parser.LT,
    parser.GT,
    parser.LE,
    parser.GE,
}
booleanOp = {parser.AND, parser.OR, parser.XOR, parser.XNOR, parser.IMPLIES, parser.IFF}


def spec_to_bdd(model, spec):
    """
    Given a formula `spec` with no temporal operators, returns a BDD equivalent to
    the formula, that is, a BDD that contains all the states of `model` that
    satisfy `spec`
    """
    bddspec = pynusmv.mc.eval_simple_expression(model, str(spec))
    return bddspec


def is_boolean_formula(spec):
    """
    Given a formula `spec`, checks if the formula is a boolean combination of base
    formulas with no temporal operators.
    """
    if spec.type in basicTypes:
        return True
    if spec.type == specTypes["NOT"]:
        return is_boolean_formula(spec.car)
    if spec.type in booleanOp:
        return is_boolean_formula(spec.car) and is_boolean_formula(spec.cdr)
    return False


def check_GF_formula(spec):
    """
    Given a formula `spec` checks if the formula is of the form GF f, where f is a
    boolean combination of base formulas with no temporal operators.
    Returns the formula f if `spec` is in the correct form, None otherwise
    """
    # check if formula is of type GF f_i
    if spec.type != specTypes["OP_GLOBAL"]:
        return False
    spec = spec.car
    if spec.type != specTypes["OP_FUTURE"]:
        return False
    if is_boolean_formula(spec.car):
        return spec.car
    else:
        return None


def parse_react(spec):
    """
    Visit the syntactic tree of the formula `spec` to check if it is a reactive formula,
    that is wether the formula is of the form

                    GF f -> GF g

    where f and g are boolean combination of basic formulas.

    If `spec` is a reactive formula, the result is a pair where the first element is the
    formula f and the second element is the formula g. If `spec` is not a reactive
    formula, then the result is None.
    """
    # the root of a spec should be of type CONTEXT
    if spec.type != specTypes["CONTEXT"]:
        return None
    # the right child of a context is the main formula
    spec = spec.cdr
    # the root of a reactive formula should be of type IMPLIES
    if spec.type != specTypes["IMPLIES"]:
        return None
    # Check if lhs of the implication is a GF formula
    f_formula = check_GF_formula(spec.car)
    if f_formula == None:
        return None
    # Create the rhs of the implication is a GF formula
    g_formula = check_GF_formula(spec.cdr)
    if g_formula == None:
        return None
    return (f_formula, g_formula)


def check_react_spec(spec):
    """
    Return whether the loaded SMV model satisfies or not the GR(1) formula `spec`,
    i.e., whether all executions of the model satisfy `spec`.

    Returns:
      - (True, None) if the formula is satisfied by the model;
      - (False, execution) if the formula is violated, where `execution` is a looping
        counterexample as a tuple of alternating state and input dicts;
      - None if `spec` is not a reactive formula.
    """
    # 1. Quick syntactic check: is it a reactive (GF f -> GF g) formula?
    if parse_react(spec) is None:
        return None

    # 2. Perform LTL model checking with counterexample explanation
    sat, cex_data = pynusmv.mc.check_explain_ltl_spec(spec)

    # 3. If satisfied, return immediately
    if sat:
        return (True, None)

    # 4. Build execution and detect loop from returned cex_data format
    # cex_data may be provided either as (states_list, inputs_list, loop_idx)
    # or as a flat tuple of alternating state/input dicts ending with state.
    if isinstance(cex_data, tuple) and len(cex_data) == 3 and all(not isinstance(x, dict) for x in cex_data):
        # original format: separate lists and loop index
        raw_states, raw_inputs, loop_pos = cex_data
        def bdd_to_dict(bdd_assign):
            return {var: bdd_assign[var] for var in bdd_assign}
        states = [bdd_to_dict(s) for s in raw_states]
        inputs = [bdd_to_dict(i) for i in raw_inputs]
    else:
        # flat alternating dicts: state, input, state, input, ..., state
        flat = list(cex_data)
        states = flat[0::2]
        inputs = flat[1::2]
        # detect loop: the last state repeats an earlier one
        last = states[-1]
        try:
            loop_pos = states.index(last)
        except ValueError:
            loop_pos = len(states) - 1
        # already plain dicts

    # Assemble alternating execution: state, input, state, ... ending with state
    execution = []
    for idx, st in enumerate(states):
        execution.append(st)
        if idx < len(inputs):
            execution.append(inputs[idx])

    # Close the loop by repeating the state at loop_pos
    if 0 <= loop_pos < len(states):
        execution[-1] = states[loop_pos]

    return (False, tuple(execution))
if len(sys.argv) != 2:
    print("Usage:", sys.argv[0], "filename.smv")
    sys.exit(1)

pynusmv.init.init_nusmv()
filename = sys.argv[1]
pynusmv.glob.load_from_file(filename)
pynusmv.glob.compute_model()
type_ltl = pynusmv.prop.propTypes["LTL"]
for prop in pynusmv.glob.prop_database():
    spec = prop.expr
    print(spec)
    if prop.type != type_ltl:
        print("property is not LTLSPEC, skipping")
        continue
    res = check_react_spec(spec)
    if res == None:
        print("Property is not a GR(1) formula, skipping")
    if res[0] == True:
        print("Property is respected")
    elif res[0] == False:
        print("Property is not respected")
        print("Counterexample:", res[1])

pynusmv.init.deinit_nusmv()
