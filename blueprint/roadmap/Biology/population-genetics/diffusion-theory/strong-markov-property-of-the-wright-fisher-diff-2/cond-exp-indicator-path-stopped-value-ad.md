# Strong Markov property with selection for whole-path functionals

Let `κ = (κ_t)_{t ≥ 0}` be a [Feller](is-feller-family.md) family of Markov kernels on `[0, 1]`, `μ`
a finite measure on a measurable space `Ω`, `(ℱ_t)_{t ≥ 0}` a filtration, `σ` a real number and `X`
a [Wright–Fisher diffusion with selection `σ`, Markov for `κ`](is-selection-markov.md), with respect
to `(ℱ_t)` and `μ`: `X` is a continuous `(ℱ_t)`-adapted solution with values in `[0, 1]` of the
[martingale problem](../fixation-and-absorption-in-the-wright-fisher-dif/is-wright-fisher-solution.md)
with selection `σ`, and `μ[g(X_t) | ℱ_s] = ∫ g(y) κ_{t - s}(X_s, dy)` `μ`-almost everywhere for all
times `0 ≤ s ≤ t` and every continuous `g : [0, 1] → ℝ`. Let `τ` be an `(ℱ_t)`-stopping time with
values in `[0, ∞]` and `ℱ_τ` its σ-algebra. Suppose moreover that `κ` satisfies the
Chapman–Kolmogorov equations `κ_{s + t}(x, ·) = ∫ κ_t(y, ·) κ_s(x, dy)`. Then for every bounded
measurable `F` on the
[sample paths](../construction-of-the-neutral-wright-fisher-diffus/sample-path.md) `[0, ∞) → [0, 1]`
(product σ-algebra),

`μ[1_{τ < ∞} F((X_{τ + u})_{u ≥ 0}) | ℱ_τ] = 1_{τ < ∞} ∫ F dP^κ_{X_τ}` `μ`-almost everywhere,

where `P^κ_y` is the
[path measure](../../../../Probability/markov-chains/markov-processes-from-transition-semigroups/path-measure.md)
of `κ` with input `y`. Here `y` is the input of the kernel construction: the time-`0` marginal of
`P^κ_y` is `κ_0(y, ·)`. This marginal is the point mass at the input for every input exactly when
`κ_0` is the identity kernel, which is not assumed here; the Chapman–Kolmogorov equations alone do
not imply it (the constant family `κ_t(x, ·) = δ_0` satisfies them, and `κ_0(1, ·) = δ_0`).

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986),
  ch. 4, §1 and Thm. 2.7.
- D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*, 3rd ed., Springer (1999), ch.
  III, §1 and §3.
