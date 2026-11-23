# Sufficient conditions for asymptotic normality of Tajima's D

Along a countably generated filter `l` (an asymptotic regime, such as a sequence of data sets
with a growing number of independent loci), let the `k`-th data set have `n k` genes, mean
number of pairwise differences `π k` and `S k` segregating sites, all real random variables on
one probability space, with each `S k` almost everywhere measurable, and let `r k > 0` be
scalings. Write `a₁, e₁, e₂` for Tajima's constants for `n k` genes. If

* the scaled numerator satisfies a central limit theorem,
  `r k (π k - S k / a₁) →ᵈ N(0, σ²)`, and
* the variance estimator is ratio-consistent at the same scale,
  `r k² (e₁ S k + e₂ S k (S k - 1)) → σ²` in probability, with `σ² > 0`,

then [Tajima's D](../tajima-s-d/tajima-d.md) satisfies `D k →ᵈ N(0, 1)` (Slutsky's theorem).
The limits in distribution are random variables with the stated Gaussian laws on a second
probability space.
