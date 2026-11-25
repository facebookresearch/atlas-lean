# The mean of Tajima's D under the neutral model

Let `μ` be a probability measure, `n ≥ 4`, `θ` real, and let `T_k` be
[Kingman holding times](../../coalescent-theory/kingman-s-coalescent-and-watterson-s-estimator/kingman-times.md)
of a sample of `n` genes under `μ` (mutually independent, with `T_k` exponential of rate
`k (k - 1) / 2` for `2 ≤ k ≤ n`), with
[total branch length](../../coalescent-theory/kingman-s-coalescent-and-watterson-s-estimator/total-length.md)
`L`, and let `𝒢` be a sub-σ-algebra. Suppose that

- the number of segregating sites `S` is square integrable, with `S = 0` or `S ≥ 1` almost
  surely and `E[S | 𝒢] = (θ / 2) L` almost surely;
- for each [pair](../../coalescent-theory/segregating-sites-and-pairwise-differences/sample-pairs.md)
  `s` of genes, `τ_s` is exponential with rate `1`, and `D_s` is square integrable with
  `E[D_s | 𝒢] = θ τ_s` almost surely.

Let `π` be the
[mean number of pairwise differences](../../coalescent-theory/segregating-sites-and-pairwise-differences/mean-pair-diff.md)
of the `D_s` and `N = π - S / a₁`. Then the mean of [Tajima's D](../tajima-s-d/tajima-d.md) is
the covariance of `N` with the reciprocal denominator: `E[D] = Cov(N, 1 / √(e₁ S + e₂ S (S - 1)))`.
Whether this covariance vanishes is a property of the joint law of `(π, S)`, not of the first two
moments of `N`; see the [counterexample](exists-integral-tajima-d-ne.md).

Where `S = 0`, which has positive probability under the neutral model, `D = N / √0 = 0` by the
conventions `√0 = 0` and `x / 0 = 0` (Tajima's D is undefined there), so `E[D] = E[D 1{S ≥ 1}]`,
an unnormalised mean, not the conditional mean of `D` given `S ≥ 1`.
