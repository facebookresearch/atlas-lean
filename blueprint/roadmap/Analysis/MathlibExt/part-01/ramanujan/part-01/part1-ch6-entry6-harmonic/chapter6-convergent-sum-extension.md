---
article_id: af_5d8927dc770924cf29b44515
declaration: def
origin: cited
statement: formalized
lean: MathlibExt.Analysis.Ramanujan.Part1Ch6.Entry6Harmonic.chapter6ConvergentSumExtension
---

# Chapter6 Convergent Sum Extension

Ramanujan's extension of the partial sums of `f` to real arguments,
`F(x) = ∑_{k ≥ 1} f(k) - ∑_{k ≥ 1} f(k + x)`. When the series converge it agrees with
`chapter6PartialSum f m` at `x = m` (`chapter6ConvergentSumExtension_natCast`).

## Depends on

This node has no prerequisites.

## Proof depends on

- [Chapter6 Derived Series Constant](chapter6-derived-series-constant.md)
- [Chapter6 Shifted Derived Series Term](chapter6-shifted-derived-series-term.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.Ramanujan.Part1Ch6Entry6Harmonic](../../../../../../../sources/v2/MathlibExt.md)
