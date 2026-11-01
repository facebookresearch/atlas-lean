---
declaration: theorem
origin: cited
statement: formalized
lean: MetaMathlibExt.soCS_odd_span
---

# So CS odd span

For each odd `N ≥ 3` there is a SoCS solution `(a, b, c)` with
`c - a = N`, and an infinite family of SoCS solutions with odd span, all
lying in the plane `(b - c) * x + (c - a) * y + (a - b) * z = 0` determined
by that solution (the plane through `(a, b, c)` and the line `x = y = z`, as
in Proposition 1). Partial scope: the paper additionally states that this
plane is unique for each `N`; that uniqueness clause is not encoded here.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.ConsecutiveSquaresWanted](../../../../../sources/v2/WantedExt.md)
- Anderson, Woodall and Zaharescu, *Arithmetic Polygons and Sums of Consecutive Squares*, INTEGERS 26 (2026), Article A1, Theorem 2 (`integers-2026-A1-thm-2`), verified against arXiv:2411.08398.
