---
article_id: af_2e551085dda6dbfeb2a40703
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.initialSegmentMean
---

# Taylor Initial Mean

Initial-segment mean `m(a, n)` from Eq. (`eq:mean`): `(1 / n)` times the sum
of `a(j)` over `j = 1, ..., n`, coerced to `ℝ`.

Total in Lean (`n = 0` gives `0` via inverse-zero); the source invokes it for
`n ≥ 2` with `ℕ = {1, 2, ...}`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Analysis.Asymptotics.TaylorInitialMean](../../../../../sources/v2/MathlibExt.md)
- Joel E. Cohen, *Variance Functions of Asymptotically Exponentially Increasing Integer Sequences Go Beyond Taylor's Law*, Journal of Integer Sequences 25 (2022), Article 22.9.3, mean/variance definitions, lines 119–124, equation `eq:mean` at line 122, <https://cs.uwaterloo.ca/journals/JIS/VOL25/Cohen/cohen13.tex>.
