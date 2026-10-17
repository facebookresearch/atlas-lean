---
article_id: af_fce40883a0376abe66915da2
declaration: def
origin: cited
statement: formalized
lean: MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry9Odd.entry9_P
---

# Entry9 P

Ramanujan's Entry 9(i) product series `P(a, b, x; z)`: the `j`-th summand is
`(-b)^j * x^(j+1)` divided by `∏ r ∈ Finset.range (j + 1), (z + a + b * (r + 1))`.

This is a totalized extension of the source expression: Lean's division sends `c / 0` to `0`,
and `∑'` of a non-summable family to `0`. Hence at a pole of the source expression -- for
example `a = 0`, `b = 1`, `x = 1`, `z = -1`, where every product contains the vanishing
factor `z + a + b * (0 + 1) = 0` -- every quotient, and so `entry9_P` itself, evaluates to
`0`, whereas the source expression has a singularity there. Off the poles, with
`w = (z + a) / b` in the sector `|arg w| ≤ π - ε` and `‖w‖ > 0`, `entry9_P_closed` identifies
`entry9_P` with the source's closed form.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Ramanujan.Part1Ch3Entry9Odd](../../../../../../../sources/v2/MathlibExt.md)
