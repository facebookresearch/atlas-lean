# Conditions for asymptotic normality of Tajima's `D`

Along a filter `l` (an asymptotic
regime, e.g. a growing number of independent loci), let the `k`-th data set have `n k` genes,
pairwise-difference mean `π k` and `S k` segregating sites, and let `r k > 0` be scalings. If

* the scaled numerator satisfies a central limit theorem,
  `r k (π k - S k / a₁) →ᵈ N(0, σ²)`, and
* the variance estimator is ratio-consistent at the same scale,
  `r k² (e₁ S k + e₂ S k (S k - 1)) → σ²` in probability, with `σ² > 0`,

then `D k →ᵈ N(0, 1)` (Slutsky's theorem). The conclusion is stated for any random variable `W`
with the standard Gaussian law.
