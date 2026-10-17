---
article_id: af_11945c25fa87aa2c54168fe2
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.initialSegmentSampleVariance
---

# Taylor Initial Sample Variance

Unbiased initial-segment sample variance `v(a, n) = (1 / (n - 1)) * ∑_{j=1}^n (a(j) - m(a,
n))^2`
in `ℝ` for Taylor's variance-to-mean power law: the first equality of `eq:varexpanded`,
with mean `m(a, n) = (1 / n) * ∑_{j=1}^n a(j)` from `eq:mean` inlined.

Indices run from `1` through `n`; total in Lean (`n = 0` gives `0` via
inverse-zero); the source invokes it for `n ≥ 2` with `ℕ = {1, 2, ...}`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Analysis.Asymptotics.TaylorInitialSampleVariance](../../../../../sources/v2/MathlibExt.md)
- Joel E. Cohen, *Variance Functions of Asymptotically Exponentially Increasing Integer Sequences Go Beyond Taylor's Law*, Journal of Integer Sequences 25 (2022), Article 22.9.3, mean/variance definitions, lines 119–124, equation `eq:mean` at line 122, first equality of `eq:varexpanded` at line 123 (label at line 124), <https://cs.uwaterloo.ca/journals/JIS/VOL25/Cohen/cohen13.tex>.
