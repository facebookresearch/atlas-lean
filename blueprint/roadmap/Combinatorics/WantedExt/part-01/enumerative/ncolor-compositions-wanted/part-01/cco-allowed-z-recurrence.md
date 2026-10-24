---
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.Combinatorics.Enumerative.NColorCompositionsWanted.ccoAllowedZ_recurrence
---

# Proposition 1

**Proposition 1**, recurrence: for `b ≥ 1` and `n ≥ 2`,
`cco_{b,b+1}(n) = cco_{b,b+1}(n-1) + cco_{b,b+1}(n-b) +
cco_{b,b+1}(n-b-1)` (the printed statement says positive `n`;
at `n = 1` the identity fails, e.g. `cco_{1,2}(1) = 1 ≠ 2`).

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Combinatorics.Enumerative.NColorCompositionsWanted](../../../../../../../sources/v2/WantedExt.md)
- Brian Hopkins and Hua Wang, "Allowing or Prohibiting Two Consecutive Colors in `n`-Color Compositions", Proposition 1.
