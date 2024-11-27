import z3


def add_new_char(coordinates: tuple[int, int], solver: z3.Solver) -> z3.ArithRef:
    """
    Create a new character at a given grid point, represented by its ascii value

    The constraints governing the character will be encoded in the solver
    """
    x, y = coordinates
    new_char = z3.Int(f"char_{x}_{y}")
    # Valid characters are uppercase or lowercase letters
    solver.add(
        z3.Or(
            z3.And(new_char >= ord("A"), new_char <= ord("Z")),
            z3.And(new_char >= ord("a"), new_char <= ord("z")),
        )
    )
    return new_char


def add_distinctness_constraint(
    solver: z3.Solver, all_vars: list[list[z3.ArithRef]]
) -> None:
    """Add the constraint that all variables take distinct values"""
    solver.add(z3.Distinct([v for row in all_vars for v in row]))


def add_word_constraints(
    word: str, solver: z3.Solver, all_vars: list[list[z3.ArithRef]]
) -> None:
    """Add the constraint that the desired word appears somewhere in the solver"""
    # Get information about the size of the grid, convert word into list of ints
    height, width, wlen = len(all_vars), len(all_vars[0]), len(word)

    # Word has to appear at some point, either horizontally, vertically, or diagonally
    constraints = []

    # Horizontal constraints
    for y in range(height):
        for x0 in range(0, width - wlen + 1):
            cons = []
            for i, c in enumerate(word):
                var = all_vars[y][x0 + i]
                cons.append(z3.Or(var == ord(c.upper()), var == ord(c.lower())))
            constraints.append(z3.And(*cons))

    # Vertical constraints
    for y0 in range(0, height - wlen + 1):
        for x in range(0, width):
            cons = []
            for i, c in enumerate(word):
                var = all_vars[y0 + i][x]
                cons.append(z3.Or(var == ord(c.upper()), var == ord(c.lower())))
            constraints.append(z3.And(*cons))

    # Diagonal constraints
    for y0 in range(0, height - wlen + 1):
        for x0 in range(0, width - wlen + 1):
            cons = []
            for i, c in enumerate(word):
                var = all_vars[y0 + i][x0 + i]
                cons.append(z3.Or(var == ord(c.upper()), var == ord(c.lower())))
            constraints.append(z3.And(*cons))

    # Require one of these constraints to be satisfied for this word
    solver.add(z3.Or(*constraints))


def print_unique_solutions(
    solver: z3.Solver, all_vars: list[list[z3.ArithRef]]
) -> None:
    """Print all the unique solutions to the crossword layout"""
    result = solver.check()
    num_results = 0

    # Start enumerating through the different solutions
    while result == z3.sat:
        num_results += 1
        model = solver.model()

        # Get values for all our variables and get constraints for next unique solution
        constraints = []
        for rows in all_vars:
            row_vals = []
            for var in rows:
                # Get a specific value for this variable in this row
                v = chr(model.evaluate(var, model_completion=True).as_long()).upper()
                row_vals.append(v)
                # Constraint saying this value shouldn't be repeated at this spot
                constraints.append(z3.And(var != ord(v), var != ord(v.lower())))
            print("".join(row_vals))

        # Check for the next unique solution
        solver.add(z3.Or(constraints))
        result = solver.check()
        print()
    print(f"{num_results} solutions possible.")


if __name__ == "__main__":
    solver = z3.Solver()
    width, height = 4, 4
    word_list = ["JMN", "AMN", "NLVN", "JEM", "TSC", "FF", "O"]

    # Add all the variables, make them distinct
    all_vars = [
        [add_new_char((y, x), solver) for x in range(width)] for y in range(height)
    ]
    add_distinctness_constraint(solver, all_vars)

    # Add the constraints on the words we want
    for word in word_list:
        add_word_constraints(word, solver, all_vars)

    # Solve the constraints and print out all solutions
    print_unique_solutions(solver, all_vars)
