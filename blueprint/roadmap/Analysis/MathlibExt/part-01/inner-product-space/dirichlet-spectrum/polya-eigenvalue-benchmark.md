---
article_id: af_ce282a79eac17820ddeef0d9
declaration: def
origin: cited
statement: formalized
lean: EuclideanLaplacian.polyaEigenvalueBenchmark
---

# Polya Eigenvalue Benchmark

Zero-based eigenvalue benchmark at index `j`: `(2π)²` times the real power
of the one-based eigenvalue number `((j + 1 : ℕ) : ℝ)` divided by
`ωₙ |Ω|`, with exponent `2 / (n : ℝ)`. The one-based numerator is kept explicit
because `NonnegativeDiscreteSpectrum` is zero-based.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Domain Volume](domain-volume.md)
- [Unit Ball Volume](unit-ball-volume.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.InnerProductSpace.DirichletSpectrum](../../../../../../sources/v2/MathlibExt.md)
