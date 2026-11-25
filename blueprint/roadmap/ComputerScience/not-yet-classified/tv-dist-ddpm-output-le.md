# Sampling guarantee for score-based diffusion (DDPM)

There are universal constants
`C, c > 0` such that the following holds. Let `q` be a probability measure on `ℝ^d` whose
forward Ornstein–Uhlenbeck marginals `q_t` have positive differentiable densities `ρ t` (smooth
at `t = 0`) with `L`-Lipschitz scores, `L ≥ 1`, finite second moment `m₂²`, and finite KL
divergence from the standard Gaussian `γ`. Let `T > 0`, `N ≥ 1`, `h = T / N ≤ c / L`, and let
measurable estimates `s k` satisfy `E_{q_{kh}} ‖s k - ∇ log ρ (kh)‖² ≤ ε²` for `k = 1, …, N`.
Then the output law `p_T` of the sampler satisfies
`TV(p_T, q) ≤ C (√(KL(q ‖ γ)) e^{-T} + (L √(d h) + L m₂ h) √T + ε √T)`.

Mathlib's `tvDist` is twice the `sup_A |μ A - ν A|` distance; the factor is absorbed in `C`.

## Sources

- S. Chen, S. Chewi, J. Li, Y. Li, A. Salim and A. R. Zhang, arXiv:2209.11215v3, Theorem 2 with Assumptions 1-3. Full support and a smooth density of `q` are the standing assumptions of the source's Section 2; finiteness of the KL divergence is assumption A3 of its introduction (the bound is vacuous without it); measurability of the estimates is implicit in the source (it makes `p_T` a law).
