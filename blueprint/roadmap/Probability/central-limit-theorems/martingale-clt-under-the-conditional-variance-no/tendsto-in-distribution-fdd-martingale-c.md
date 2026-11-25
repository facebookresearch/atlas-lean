# Finite-dimensional convergence under the conditional-variance normalization

Assume `∀ n k, MemLp (X n k) 2 μ`, `∀ s, Measurable (Z s)` and `∀ (I : Finset ι) (c : I → ℝ), P'.map (fun ω => ∑ s : I, c s * Z s ω) = gaussianReal 0 (∑ s : I, ∑ u : I, c s * c u * A (min (s : ι) u)).toNNReal`.

Let
`S n s = ∑_{k < N n s} X n k` along a linearly ordered time axis, with `N n` monotone and
`N n s ≤ r n`. If the predictable quadratic variation up to `N n s` tends to `A s` in probability
for every `s`, the predictable quadratic variation of the whole row (up to `r n`) converges in
probability to some `V`, and the conditional Lindeberg condition holds on the whole row, then
the finite-dimensional distributions of `S n` converge to those of any process `Z` with centered
Gaussian finite-dimensional laws of covariance `A (min s u)`.

The terminal hypothesis `hpqvEnd` is automatic when the row ends at a time of the axis
(`r n = N n s₁`), as in `tendstoInDistribution_fdd_martingaleDifference_floor_condVar`. It is a
proof convenience, not a sharp condition: the cut is built from the predictable quadratic
variation of the whole row because the fdd interface of McLeish's theorem wants `N n s ≤ r n`
and the quadratic-variation limit at every `s`; cutting at `N n (max I)` after re-indexing the
time axis to `I` would remove it.

The proof is the cut of `tendstoInDistribution_martingale_condVar` (at level `|V| + 1`)
followed by `tendstoInDistribution_fdd_martingale_mcLeish`.
