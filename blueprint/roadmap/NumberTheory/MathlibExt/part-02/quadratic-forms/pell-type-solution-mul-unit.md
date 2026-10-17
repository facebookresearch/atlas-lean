---
article_id: af_9127b56fc5f090252c9c31a1
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.pellType_solution_mul_unit
---

# Pell Type Solution Mul Unit

Multiplying a solution `(T, U)` of `a * T ^ 2 - b * U ^ 2 = c` by a unit
`(x, y)` of `x ^ 2 - a * b * y ^ 2 = 1` yields the solution
`(T * x + b * U * y, a * T * y + U * x)`.

The source iterates this step under the assumption that `ab > 1` is not a
square to obtain infinitely many solutions. That infinitude claim needs further
nondegeneracy hypotheses (for `T = U = c = 0` every iterate is `(0, 0)`) and is
not formalized here; the single-step identity is pure algebra
(multiplicativity of the norm form) needing no hypotheses beyond the two
equations.
Proves `Wanted` entry `pellType_solution_mul_unit`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.QuadraticForms.PellTypeSolutionMulUnit](../../../../../sources/v2/MathlibExt.md)
- E. L. Roettger and H. C. Williams, "Some Remarks Concerning the Lucas-Lehmer Primality Test," Journal of Integer Sequences 28 (2025), Article 25.2.5, Theorem (label PellTheorem, an observation of Euler), equation (label DioEq), lines 605–614, <https://cs.uwaterloo.ca/journals/JIS/VOL28/Roettger/roettger15.tex>
