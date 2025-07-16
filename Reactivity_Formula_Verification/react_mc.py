import pynusmv
import sys
from pynusmv_lower_interface.nusmv.parser import parser 
from collections import deque
from pynusmv.dd import BDD
from pprint import pprint
from pynusmv.fsm import BddFsm
from pynusmv import utils
from collections import deque
from pynusmv.dd import BDD, State, Inputs
from pynusmv.fsm import BddFsm
from typing import List, Tuple 
from collections import deque
from pynusmv.dd import BDD, State, Inputs
from pynusmv.fsm import BddFsm
from typing import List, Tuple

specTypes = {'LTLSPEC': parser.TOK_LTLSPEC, 'CONTEXT': parser.CONTEXT,
    'IMPLIES': parser.IMPLIES, 'IFF': parser.IFF, 'OR': parser.OR, 'XOR': parser.XOR, 'XNOR': parser.XNOR,
    'AND': parser.AND, 'NOT': parser.NOT, 'ATOM': parser.ATOM, 'NUMBER': parser.NUMBER, 'DOT': parser.DOT,

    'NEXT': parser.OP_NEXT, 'OP_GLOBAL': parser.OP_GLOBAL, 'OP_FUTURE': parser.OP_FUTURE,
    'UNTIL': parser.UNTIL,
    'EQUAL': parser.EQUAL, 'NOTEQUAL': parser.NOTEQUAL, 'LT': parser.LT, 'GT': parser.GT,
    'LE': parser.LE, 'GE': parser.GE, 'TRUE': parser.TRUEEXP, 'FALSE': parser.FALSEEXP
}

basicTypes = {parser.ATOM, parser.NUMBER, parser.TRUEEXP, parser.FALSEEXP, parser.DOT,
              parser.EQUAL, parser.NOTEQUAL, parser.LT, parser.GT, parser.LE, parser.GE}
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
    if spec.type == specTypes['NOT']:
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
    if spec.type != specTypes['OP_GLOBAL']:
        return False
    spec = spec.car
    if spec.type != specTypes['OP_FUTURE']:
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
    if spec.type != specTypes['CONTEXT']:
        return None
    # the right child of a context is the main formula
    spec = spec.cdr
    # the root of a reactive formula should be of type IMPLIES
    if spec.type != specTypes['IMPLIES']:
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

def repeat_check(fsm: BddFsm, f: BDD, g: BDD) -> Tuple[bool, List[State | Inputs]]:
    """
    Checks for violations of the reactive specification GF f -> GF g
    Returns (violation_found, counterexample_trace)
    """
    # Initialize reachability computation
    reachable_states = fsm.init
    frontier = fsm.init
    reachability_trace = [frontier]
    
    # Forward reachability analysis
    while not frontier.is_false():
        next_frontier = fsm.post(frontier) - reachable_states
        reachability_trace.append(next_frontier)
        reachable_states = reachable_states | next_frontier
        frontier = next_frontier

    # Identify problematic states: reachable, satisfy f, violate g
    negated_g = ~g
    candidate_states = reachable_states & f & negated_g
    
    # Search for cycles in the bad region
    while not candidate_states.is_false():
        backward_frontier = fsm.pre(candidate_states) & negated_g
        backward_reachable = BDD.false(fsm)
        
        while not backward_frontier.is_false():
            backward_reachable = backward_reachable | backward_frontier
            
            # Check if we can form a cycle
            if candidate_states <= backward_reachable:
                cycle_part = construct_cycle(fsm, candidate_states, backward_reachable)
                prefix_part = construct_prefix(fsm, reachability_trace, cycle_part[0])
                return True, prefix_part + cycle_part
                
            backward_frontier = (fsm.pre(backward_frontier) & negated_g) - backward_reachable
        
        # Refine candidate states
        candidate_states = candidate_states & backward_reachable
        
    return False, None

def locate_cycle_state(fsm: BddFsm, candidates: BDD, reachable_back: BDD) -> Tuple[State, List[BDD]]:
    """
    Identifies a concrete state within a cycle and computes forward frontiers
    """
    selected_state = fsm.pick_one_state(candidates)
    cycle_found = False
    
    while not cycle_found:
        forward_step = fsm.post(selected_state) & reachable_back
        visited_set = BDD.false(fsm)
        forward_frontiers = [forward_step]
        
        while not forward_step.is_false():
            visited_set = visited_set | forward_step
            forward_step = (fsm.post(forward_step) & reachable_back) - visited_set
            forward_frontiers.append(forward_step)
        
        # Check if the selected state is reachable from the visited set
        intersection = visited_set & candidates
        cycle_found = selected_state <= intersection
        if not cycle_found:
            selected_state = fsm.pick_one_state(intersection)
    
    return selected_state, forward_frontiers

def construct_cycle(fsm: BddFsm, candidates: BDD, reachable_back: BDD) -> List[State | Inputs]:
    """
    Constructs the repeating cycle portion of the counterexample
    """
    cycle_state, forward_frontiers = locate_cycle_state(fsm, candidates, reachable_back)
    cycle_length = -1
    
    # Determine cycle length by finding where the cycle state appears
    for idx, frontier in enumerate(forward_frontiers):
        if cycle_state <= frontier:
            cycle_length = idx
            break
    
    cycle_sequence = [cycle_state]
    current_state = cycle_state
    
    # Reconstruct cycle backwards
    for step in range(cycle_length - 1, -1, -1):
        predecessor_states = fsm.pre(current_state) & forward_frontiers[step]
        predecessor_state = fsm.pick_one_state(predecessor_states)
        transition_inputs = fsm.get_inputs_between_states(predecessor_state, current_state)
        cycle_sequence = [predecessor_state, fsm.pick_one_inputs(transition_inputs)] + cycle_sequence
        current_state = predecessor_state
    
    # Add final transition to complete the cycle
    final_inputs = fsm.get_inputs_between_states(cycle_state, current_state)
    return [cycle_state, fsm.pick_one_inputs(final_inputs)] + cycle_sequence

def construct_prefix(fsm: BddFsm, trace: List[BDD], target_state: State) -> List[State | Inputs]:
    """
    Constructs the prefix path from initial state to cycle entry point
    """
    target_level = -1
    
    # Find the reachability level of the target state
    for level, frontier in enumerate(trace):
        if target_state <= frontier:
            target_level = level
            break
    
    path_sequence = []
    current_state = target_state
    
    # Reconstruct path backwards from target to initial state
    for level in range(target_level - 1, -1, -1):
        predecessor_states = fsm.pre(current_state) & trace[level]
        predecessor_state = fsm.pick_one_state(predecessor_states)
        transition_inputs = fsm.get_inputs_between_states(predecessor_state, current_state)
        path_sequence = [predecessor_state, fsm.pick_one_inputs(transition_inputs)] + path_sequence
        current_state = predecessor_state
    
    return path_sequence

def check_react_spec(specification):
    """
    Main function to check reactive specifications
    """
    system_model = pynusmv.glob.prop_database().master.bddFsm
    parsing_result = parse_react(specification)
    
    if parsing_result is None:
        return None
        
    antecedent, consequent = parsing_result
    antecedent_bdd = spec_to_bdd(system_model, antecedent)
    consequent_bdd = spec_to_bdd(system_model, consequent)
    
    violation_detected, counterexample = repeat_check(system_model, antecedent_bdd, consequent_bdd)
    
    if not violation_detected:
        return (True, None)
    
    # Format the counterexample for output
    formatted_execution = []
    for element in counterexample:
        if isinstance(element, State):
            formatted_execution.append(element.get_str_values())
        elif isinstance(element, Inputs):
            formatted_execution.append(element.get_str_values())
    
    return (False, tuple(formatted_execution))


if len(sys.argv) != 2:
    print("Usage:", sys.argv[0], "filename.smv")
    sys.exit(1)

pynusmv.init.init_nusmv()
filename = sys.argv[1]
pynusmv.glob.load_from_file(filename)
pynusmv.glob.compute_model()
type_ltl = pynusmv.prop.propTypes['LTL']
for prop in pynusmv.glob.prop_database():
    spec = prop.expr
    print(spec)
    if prop.type != type_ltl:
        print("property is not LTLSPEC, skipping")
        continue
    res = check_react_spec(spec)
    if res == None:
        print('Property is not a GR(1) formula, skipping')
    if res[0] == True:
        print("Property is respected")
    elif res[0] == False:
        print("Property is not respected")
        print("Counterexample:", res[1])

pynusmv.init.deinit_nusmv()





