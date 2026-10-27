---
article_id: af_78cdc891b51b61cacb5cbaba
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.Convex.LPDuality.strong_linear_programming_duality
---

# Linear Programming Duality

Strong LP duality: a feasible bounded-above primal
`max { c ⬝ᵥ x | x ≥ 0, A *ᵥ x ≤ b }` admits optimal primal and dual points
`x ≥ 0`, `A *ᵥ x ≤ b`, `y ≥ 0`, `c ≤ Aᵀ *ᵥ y` with equal values
`c ⬝ᵥ x = b ⬝ᵥ y`, certifying optimality for both.

Informal source: George B. Dantzig, *Linear Programming and Extensions*,
Princeton University Press, 1963, strong duality theorem.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Analysis.Convex.LinearProgrammingDuality](../../../../../sources/v2/MathlibExt.md)
