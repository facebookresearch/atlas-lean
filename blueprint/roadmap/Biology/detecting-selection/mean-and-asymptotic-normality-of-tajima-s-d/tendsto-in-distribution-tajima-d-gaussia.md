# Sufficient conditions for asymptotic normality of Tajima's D

Along a countably generated filter `l` (an asymptotic regime, such as a sequence of data sets
with a growing number of independent loci), let the `k`-th data set have a deterministic number
`n k` of genes, and let its mean number of pairwise differences `π k` and its number `S k` of
segregating sites be real functions on one probability space `(Ω, μ)`, each `S k` almost
everywhere measurable; let `r k > 0` be scalings. Write `a₁, e₁, e₂` for Tajima's constants for
`n k` genes. If

* the scaled numerator satisfies a central limit theorem,
  `r k (π k - S k / a₁) →ᵈ N(0, σ²)`, and
* the variance estimator is ratio-consistent at the same scale,
  `r k² (e₁ S k + e₂ S k (S k - 1)) → σ²` in probability, with `σ² > 0`,

then [Tajima's D](../tajima-s-d/tajima-d.md) satisfies `D k →ᵈ N(0, 1)` (Slutsky's theorem).
The limits in distribution are random variables with the stated Gaussian laws on a second
probability space.

Neither `n k ≥ 4` nor a positive radicand `e₁ S k + e₂ S k (S k - 1)` is assumed for any `k`. By
the conventions `√x = 0` for `x ≤ 0` and `x / 0 = 0`, `D k = 0` wherever that radicand is at most
`0`, and `S k / a₁ = 0` when `n k ≤ 1`. The convergence in probability of
`r k² (e₁ S k + e₂ S k (S k - 1))` to `σ² > 0` makes the probability of the set where the
radicand is at most `0` tend to `0`, but says nothing about that set for a given `k`.
