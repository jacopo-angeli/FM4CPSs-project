import pynusmv
import sys
from pynusmv_lower_interface.nusmv.parser import parser

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


# ----------------------------------------------------------------------------------------------
def check_react_spec(spec):
    """
    Check if a reactivity specification is satisfied by the loaded SMV model.

    Returns:
    - None if spec is not a reactivity formula
    - (True, None) if the formula is satisfied
    - (False, counterexample) if the formula is not satisfied
    """
    # Parse the reactive formula
    parse_result = parse_react(spec)
    if parse_result is None:
        return None

    f, g = parse_result
    ng = pynusmv.prop.not_(g)

    fsm_bdd = pynusmv.glob.prop_database().master.bddFsm
    f_bdd = spec_to_bdd(fsm_bdd, f)
    ng_bdd = spec_to_bdd(fsm_bdd, ng)

    # Reach-set ---------------------------------------------------------------------------
    reach_bdd = fsm_bdd.init
    new_bdd = fsm_bdd.post(reach_bdd)
    while not new_bdd.equal(reach_bdd.intersection(new_bdd)):
        reach_bdd = reach_bdd.union(new_bdd.diff(reach_bdd))
        new_bdd = fsm_bdd.post(reach_bdd)
    # -------------------------------------------------------------------------------------

    # Symbolic repeatability check of f & !g ----------------------------------------------
    recur_bdd = reach_bdd.intersection(f_bdd).intersection(ng_bdd)
    while fsm_bdd.count_states(recur_bdd) > 0:
        pre_reach_bdd = new_bdd = fsm_bdd.pre(recur_bdd).intersection(ng_bdd)
        while fsm_bdd.count_states(new_bdd) > 0:
            pre_reach_bdd = pre_reach_bdd.union(new_bdd)
            if recur_bdd.entailed(pre_reach_bdd):
                # Property is repeatable -> witness build
                # Loop head search--------------------------------------------------------
                recur_states_list = list(fsm_bdd.pick_all_states(recur_bdd))
                loop_head = recur_states_list.pop(0)
                while True:
                    Frontiers = []
                    new_bdd = fsm_bdd.post(loop_head).intersection(pre_reach_bdd)
                    R = new_bdd
                    while fsm_bdd.count_states(new_bdd) > 0:
                        R = R.union(new_bdd)
                        Frontiers.append(R)
                        new_bdd = fsm_bdd.post(new_bdd).intersection(pre_reach_bdd)
                        new_bdd = new_bdd.diff(R)
                    R = R.intersection(recur_bdd)
                    if loop_head.entailed(R):
                        break
                    else:
                        loop_head = recur_states_list.pop(0)
                # -----------------------------------------------------------------------
                # Loop body build -------------------------------------------------------
                k = 0
                while not loop_head.entailed(Frontiers[k]):
                    k += 1
                loop = [loop_head]
                trace = [loop_head.get_str_values()]
                curr = loop_head
                for i in range(k - 1, -1, -1):
                    Pred = fsm_bdd.pre(curr).intersection(Frontiers[i])
                    curr = fsm_bdd.pick_one_state(Pred)
                    trace = [
                        curr.get_str_values(),
                        fsm_bdd.pick_one_inputs(
                            fsm_bdd.get_inputs_between_states(curr, loop[0])
                        ).get_str_values(),
                    ] + trace
                    loop = [curr] + loop

                trace = [
                    loop_head.get_str_values(),
                    fsm_bdd.pick_one_inputs(
                        fsm_bdd.get_inputs_between_states(loop_head, loop[0])
                    ).get_str_values(),
                ] + trace
                loop = [loop_head] + loop
                # -------------------------------------------------------------------------
                # Loop prefix build -------------------------------------------------------
                images = list()
                counterex = pre_counterex = loop_head
                images.append(counterex)
                while not pre_counterex.intersected(fsm_bdd.init):
                    counterex = pre_counterex
                    pre_counterex = fsm_bdd.pre(counterex)
                    images.insert(0, pre_counterex)
                # -------------------------------------------------------------------------
                # trace composition -------------------------------------------------------
                trace_init = list()
                start = fsm_bdd.init  # Start from initial states
                for i in range(0, len(images) - 1):
                    start = start.intersection(images[i])
                    post = fsm_bdd.post(start).intersection(images[i + 1])
                    trace_init.append(fsm_bdd.pick_one_state(start).get_str_values())
                    trace_init.append(
                        fsm_bdd.pick_one_inputs(
                            fsm_bdd.get_inputs_between_states(start, post)
                        ).get_str_values()
                    )
                    start = post
                # -------------------------------------------------------------------------
                return (False, trace_init + trace)
            new_bdd = (fsm_bdd.pre(new_bdd).diff(pre_reach_bdd)).intersection(ng_bdd)
        recur_bdd = recur_bdd.intersection(pre_reach_bdd)
    return (True, None)
    # -------------------------------------------------------------------------------------


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
        print("Counterexample:")
        for t in res[1]:
            print(t)
pynusmv.init.deinit_nusmv()
