# Linear Programming Integrality

A basic feasible point of `A *ᵥ x ≤ b`, `0 ≤ x` is integral when `A` is
 totally unimodular and `b` is integral. The basis selects rows from `[A; -I]`,
 with right-hand side `[b; 0]`, so nonnegativity constraints are selectable.

Feasibility records the LP context; the algebraic integrality argument uses
only the nonsingular tight basis. No objective or positive dimension is
needed.
