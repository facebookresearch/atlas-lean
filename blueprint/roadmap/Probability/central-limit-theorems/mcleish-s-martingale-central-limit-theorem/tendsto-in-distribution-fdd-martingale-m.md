# Finite-dimensional convergence for martingale arrays

Assume `∀ s, Measurable (Z s)` and `∀ (I : Finset ι) (c : I → ℝ), P'.map (fun ω => ∑ s : I, c s * Z s ω) = gaussianReal 0 (∑ s : I, ∑ u : I, c s * c u * A (min (s : ι) u)).toNNReal`.

**Finite-dimensional convergence for martingale arrays** (McLeish 1974, Theorem (3.2),
finite-dimensional part of the proof, with a general variance function `A` in place of `t`).

Let `X n k` be a martingale difference array satisfying McLeish's conditions (a) and (b) on the
rows `k < r n`, and let `S n s = ∑_{k < N n s} X n k` be the partial-sum process along a
time index `s ∈ ι` (any linear order), where `N n` is monotone with `N n s ≤ r n` (for example
`N n s = ⌊n s⌋` on `[0,1]` with `r n = n`). If for every time `s` the realized quadratic
variation `∑_{k < N n s} X n k²` tends to `A s` in probability, then for every finite set of
times `I` the vector `(S n s)_{s ∈ I}` converges in distribution to `(Z s)_{s ∈ I}`, for any
process `Z` whose finite-dimensional laws are centered Gaussian with covariance
`Cov(Z s, Z u) = A (min s u)` (stated through all linear combinations, `hZ`). With `A` the
identity on `[0,1]`, `Z` is a Brownian motion; in general `Z = W ∘ A`.

The proof is the Cramér–Wold device applied to
`tendstoInDistribution_martingale_mcLeish` for the weighted array
`a n k X n k`, `a n k = ∑_{s ∈ I} c s 𝟙{k < N n s}`, whose quadratic variation is
`∑_{s,u} c s c u ∑_{k < N n (min s u)} X n k²` by monotonicity of `N n`.
