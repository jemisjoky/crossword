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


def add_word_constraint(word: str, solver: z3.Solver) -> None:
    """Add the constraint that the desired word appears somewhere in the solver"""


def print_unique_solutions(
    solver: z3.Solver, all_vars: list[list[z3.ArithRef]]
) -> None:
    """Print all the unique solutions to the crossword layout"""
    result = solver.check()
    while result == z3.sat:
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


if __name__ == "__main__":
    solver = z3.Solver()
    width, height = 1, 1

    # Add all the variables
    all_vars = []
    for y in range(height):
        row = [add_new_char((y, x), solver) for x in range(width)]
        all_vars.append(row)

    # Solve the constraints and print out all solutions
    print_unique_solutions(solver, all_vars)
