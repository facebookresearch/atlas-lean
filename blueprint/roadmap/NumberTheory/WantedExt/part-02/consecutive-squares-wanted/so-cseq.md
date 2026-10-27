---
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.SoCSEq
---

# So CSEq

The Sum of Consecutive Squares (SoCS) equation
`(a+1)^2 + ⋯ + b^2 = (b+1)^2 + ⋯ + c^2`, written in cleared square-pyramidal
form `2 * P b = P a + P c` with `6 * P x = x * (x + 1) * (2 * x + 1)`.

Verified verbatim against the primary source (arXiv:2411.08398, the TeX
source of the published article): equation (1) there is
`(a+1)^2 + (a+2)^2 + ⋯ + b^2 = (b+1)^2 + (b+2)^2 + ⋯ + c^2`, restated with
`P_n = n(n+1)(2n+1)/6` as `P_b - P_a = P_c - P_b`, i.e. equation (2)
`P_a + P_c = 2 P_b`, under the range `0 < a + 1 < b < c`. The form used here
is (2) multiplied through by `6`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.ConsecutiveSquaresWanted](../../../../../sources/v2/WantedExt.md)
- Anderson, Woodall and Zaharescu, *Arithmetic Polygons and Sums of Consecutive Squares*, INTEGERS 26 (2026), Article A1, equations (1) and (2).
