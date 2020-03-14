# DeLP Program Generator (DeLPPG).
# A code made with passion and fatigue dedicated to my dear friend Maleiva, hope it could be useful.

from datetime import datetime
import random
import numpy

PL = 8  # Positive Literals (PL) || 0 <= PL
NL = 5  # Negative Literals (NL) || NL <= PL

# Maximum number of Strict Literals (SL) || SL =< PL + NL
# Strict literal are literals that are derived from only from facts or strict rules
SL = 3

# Nesting Level (Nesting) ||  It defines max length of the longest chain of defeasible rules
# that are needed to derive a literal.
# Given the DeLP program {a-<b,c; b-<c; c}, the nesting level for a is 2, for b is 1 and for c is 0.
NESTING = 3

# Body Length (BD) || It defines max length for the body of a rule (either strict or defeasible).
# BD >= 1
BD = 2

# Heads per Literal (HL) || It defines the max number of defeasible rules that share the same literal in their head.
# HL >= 1
HL = 6

# Defines the probability for an argument to be a proper defeater (or proper defeated) for a contradictory argument.
# PROPER_DEFEAT_PROB  =< 0.5 || _BLOCK_PROB = 1 - 2*PROPER_DEFEAT_PROB
PROPER_DEFEAT_PROB = 0.4


LITERALS = []  # All the literals that will be considered to generate the DeLP program.

LITERALS_PER_LEVEL = {}  # It is easier to choose literals per level when making rules.

STRICT_LITERALS_PER_LEVEL = {}  # Strict literals must be separated since the level for strict literals is 0.

PROGRAM = set([])  # The final program will be stored here.

DEPENDENCY_GRAPH = {}  # It keeps trace of the literals that are needed to derive a literal in order to avoid cycles.


def generate_strict_literals(i):
    level_literals = []
    excluded_literals = []
    if i == 0:
        if SL > 0:
            for x in range(0, random.randint(1, SL)):
                # Generate the new strict literal
                literal = get_random_literal(excluded_literals)
                level_literals.append(literal),

                # This is to ensure a consistent strict set of literals
                excluded_literals += [literal, get_complement(literal)]

                # Save the fact.
                PROGRAM.add(build_strict_rule(literal, ["true"]))
    else:
        generate_strict_literals(i - 1)

        prev_literals = []
        for x in range(i - 1, -1, -1):
            prev_literals += STRICT_LITERALS_PER_LEVEL[x]

        prev_literals_length = len(prev_literals)

        if SL - prev_literals_length > 0:
            excluded_literals = prev_literals + [get_complement(literal) for literal in prev_literals]
            # Generate strict literals for level i
            for x in range(0, random.randint(1, SL - prev_literals_length)):
                # Obtain the literal (it must be different from any previous strict literal)
                literal = get_random_literal(excluded_literals)
                level_literals.append(literal)
                excluded_literals += [literal, get_complement(literal)]

                private_excluded_literals = [literal] + get_dependent_literals([literal])

                # Build the body
                body_length = random.randint(1, min(len(prev_literals), BD))
                # First literal from the previous level
                body = [get_random_literal_from_levels(private_excluded_literals, STRICT_LITERALS_PER_LEVEL, [i - 1])]
                body_length -= 1  # Subtract the previous literal from the body

                if literal not in DEPENDENCY_GRAPH.keys():
                    DEPENDENCY_GRAPH[literal] = set([])
                DEPENDENCY_GRAPH[literal].add(body[0])  # Save dependencies

                # Following literals may be from any level
                for n in range(body_length):
                    levels = [level for level in range(i - 1, -1, -1)]
                    current_excluded_literals = body + private_excluded_literals
                    bl = get_random_literal_from_levels(current_excluded_literals, STRICT_LITERALS_PER_LEVEL, levels)
                    body.append(bl)
                    DEPENDENCY_GRAPH[literal].add(bl)  # Save dependencies

                # Save the rule
                body.sort()
                PROGRAM.add(build_strict_rule(literal, body))

    STRICT_LITERALS_PER_LEVEL[i] = level_literals


def generate_literals_from_level(i):
    if i == 0:
        generate_strict_literals(random.randint(0, NESTING))

        LITERALS_PER_LEVEL[0] = []
        for v in STRICT_LITERALS_PER_LEVEL.values():
            LITERALS_PER_LEVEL[0] += v  # Strict literals are at level 0 of derivation chain

    else:
        generate_literals_from_level(i - 1)

        level_literals = []

        # Avoid using strict literals or it complement in defeasible rules head
        strict_literals = []
        for literals_list in STRICT_LITERALS_PER_LEVEL.values():
            strict_literals += literals_list

        complementary_strict_literals = [get_complement(sl) for sl in strict_literals]
        excluded_literals = complementary_strict_literals

        current_used_literals = []
        for literals_list in LITERALS_PER_LEVEL.values():
            current_used_literals += literals_list

        # Avoid using literals that exceed the number of allowed heads per literal (HL)
        for dl in current_used_literals:
            if current_used_literals.count(dl) > HL:
                excluded_literals.append(dl)

        # Determine number of literals in this level
        # PL+NL = MAX NUMBER OF LITERALS
        # len(set(all_literals))) : NUMBER OF ALREADY USED LITERALS
        times_in_this_level = random.randint(0, max(0, (PL + NL) - len(set(current_used_literals))))

        for times in range(times_in_this_level):
            # Select literal for rule head
            literal = get_random_literal(strict_literals + excluded_literals)

            # If not possible to find a literal, we have finished.
            if literal is None:
                break

            level_literals.append(literal)

            # This list will preserve the literals that must be excluded to ensure that
            # the final argument will be consistent, and thus, ensuring the literal derivation
            private_excluded_literals = [literal, get_complement(literal)] + get_dependent_literals([literal])

            # Test if it necessary to exclude the literal for next iteration
            # to avoid exceeding the limit of rules per literal
            if level_literals.count(literal) + 1 > HL:
                excluded_literals.append(literal)

            # First literal should be from the highest previous level to try to preserve
            # the desired level for the current literal.
            body = [get_highest_random_literal(excluded_literals + private_excluded_literals, i - 1)]

            # If not possible to find a literal for for the body with level i-1, we have to
            # try with another literal.
            if body[0] is None:
                continue

            if literal not in DEPENDENCY_GRAPH.keys():
                DEPENDENCY_GRAPH[literal] = set([])  # This is a little trick (every literal is self dependent)
            DEPENDENCY_GRAPH[literal].add(body[0])

            body_length = random.randint(1, BD) - 1  # Subtract the previous literal from the body

            private_excluded_literals += [body[0], get_complement(body[0])]

            # Following literals may be from any level
            for n in range(body_length):
                levels = [level for level in range(i - 1, -1, -1)]
                current_excluded_literals = excluded_literals + private_excluded_literals
                bl = get_random_literal_from_levels(current_excluded_literals, LITERALS_PER_LEVEL, levels)
                # It is possible to exhaust literals, so in this case we must continue with the next rule
                if bl is None:
                    break
                else:
                    body.append(bl)
                    private_excluded_literals += [bl, get_complement(bl)]
                    DEPENDENCY_GRAPH[literal].add(bl)  # Save dependencies

            # Save the rule
            body.sort()  # Sort to avoid repetitions
            PROGRAM.add(build_defeasible_rule(literal, body))

        LITERALS_PER_LEVEL[i] = level_literals


def build_defeasible_rule(head, body):
    return head + " -< " + build_rule_body(body) + "."


def build_strict_rule(head, body):
    return head + " <- " + build_rule_body(body) + "."


def build_rule_body(body_literals):
    return ", ".join(body_literals)


def get_highest_random_literal(excluded_list, level):
    literal = get_random_literal_from_levels(excluded_list, LITERALS_PER_LEVEL, [level])
    if level == 0 or literal is not None:
        return literal
    else:
        if level > 0:
            return get_highest_random_literal(excluded_list, level-1)


# Returns a literal L from the specified dictionary and a random level from levels such that L does not
# belong to excluded_literals
# If it is impossible to find a literal that no belongs to the excluded list, it return None.
def get_random_literal_from_levels(excluded_literals, literals_dictionary, levels):
    literal = None
    found = False
    visited = []

    total_literals = []
    for level in levels:
        total_literals += literals_dictionary[level]

    while (not found) and (set(visited) != set(total_literals)):  # Transform to set to ignore order
        chosen_list = literals_dictionary[random.choice(levels)]
        if len(chosen_list) > 0:
            literal = random.choice(chosen_list)
            found = literal not in excluded_literals
            visited.append(literal)

    if not found:
        literal = None

    return literal


# Returns a random literal from LITERALS such that it does not belong to excluded_literals
# If it is impossible to find a literal that no belongs to the excluded list, it return None.
def get_random_literal(excluded_literals):
    literal = None
    found = False
    visited = []

    while (not found) and (set(visited) != set(LITERALS)):  # Transform to set to ignore order
        literal = random.choice(LITERALS)
        found = literal not in excluded_literals
        visited.append(literal)

    if not found:
        literal = None

    return literal


def generate_literals():
    generate_positive_literals()
    generate_negative_literals()


def generate_positive_literals():
    for x in range(PL):
        LITERALS.append("l_" + str(x))


def generate_negative_literals():
    for x in range(NL):
        LITERALS.append("~l_" + str(x))


def get_complement(literal):
    if literal[0] == "~":
        return literal[1:]
    else:
        return "~" + literal


# Returns the list of literals whose derivation depend on the derivation of the dependency_literal.
def get_dependent_literals(dependency_literals):
    direct_dependent_literals = []
    for dp in dependency_literals:
        keys = DEPENDENCY_GRAPH.keys()
        direct_dependent_literals += [x for x in keys if dp in DEPENDENCY_GRAPH[x]]

    indirect_dependent_literals = []
    if len(direct_dependent_literals) > 0:
        indirect_dependent_literals = get_dependent_literals(direct_dependent_literals)

    return direct_dependent_literals + indirect_dependent_literals


def get_defeasible_rules_for(literal, program):
    return [rule for rule in program if ("has_priority" not in rule) and ((literal + " -<") in rule) and rule[0] == literal[0]]


def set_rules_preferences(program):
    positive_literals = [lit for lit in LITERALS if lit[0] != "~"]

    for lit in positive_literals:
        for pos_rule in get_defeasible_rules_for(lit, program):
            for neg_rule in get_defeasible_rules_for(get_complement(lit), program):
                distribution = [PROPER_DEFEAT_PROB, 1 - 2 * PROPER_DEFEAT_PROB, PROPER_DEFEAT_PROB]
                n = numpy.random.choice(numpy.arange(-1, 2), p=distribution)
                pr = pos_rule[0:len(pos_rule)-1]  # Remove "." from rules
                nr = neg_rule[0:len(neg_rule)-1]
                if n != 0:
                    if n == 1:
                        program.add("has_priority((" + pr + "), (" + nr + ")).")
                    else:
                        program.add("has_priority((" + nr + "), (" + pr + ")).")


def test():
    random.seed(datetime.now())
    generate_literals()
    generate_literals_from_level(NESTING)
    set_rules_preferences(PROGRAM)
    program = list(PROGRAM)
    program.sort()
    program.insert(0, "use_criterion(rules_priorities).")  # Arguments comparison criterion
    for c in program:
        print(c)


test()
