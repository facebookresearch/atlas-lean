---
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.Combinatorics.Enumerative.NColorCompositionsWanted.ccoAllowed_eq_sum
---

# Proposition 1

**Proposition 1**, direct formula:
`cco_{b,b+1}(n) = ∑_{m=1}^n ∑_{i=0}^{n-bm}
\binom{i+m-1}{m-1} \binom{m}{n-bm-i}` (terms with `bm + i > n`
contribute `0`).

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Combinatorics.Enumerative.NColorCompositionsWanted](../../../../../../../sources/v2/WantedExt.md)
- Brian Hopkins and Hua Wang, "Allowing or Prohibiting Two Consecutive Colors in `n`-Color Compositions", Proposition 1.
