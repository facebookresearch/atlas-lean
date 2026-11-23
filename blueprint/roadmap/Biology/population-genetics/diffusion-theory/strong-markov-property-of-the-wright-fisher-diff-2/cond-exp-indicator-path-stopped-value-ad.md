# Strong Markov property with selection for whole-path functionals

Let `κ = (κ_t)_{t ≥ 0}` be a [Feller](is-feller-family.md) family of Markov kernels on `[0, 1]`, `μ`
a finite measure on a measurable space `Ω`, `(ℱ_t)_{t ≥ 0}` a filtration, `σ` a real number and `X`
a [Wright–Fisher diffusion with selection `σ`, Markov for `κ`](is-selection-markov.md), with respect
to `(ℱ_t)` and `μ`; its values lie in `[0, 1]`. Let `τ` be an `(ℱ_t)`-stopping time with values in
`[0, ∞]` and `ℱ_τ` its σ-algebra. Suppose moreover that `κ` satisfies the Chapman–Kolmogorov
equations `κ_{s + t}(x, ·) = ∫ κ_t(y, ·) κ_s(x, dy)`. Then for every bounded measurable `F` on the
[sample paths](../construction-of-the-neutral-wright-fisher-diffus/sample-path.md) `[0, ∞) → [0, 1]`
(product σ-algebra),

`μ[1_{τ < ∞} F((X_{τ + u})_{u ≥ 0}) | ℱ_τ] = 1_{τ < ∞} ∫ F dP^κ_{X_τ}` `μ`-almost everywhere,

where `P^κ_y` is the
[path measure](../../../../Probability/markov-chains/markov-processes-from-transition-semigroups/path-measure.md)
of `κ` from `y`.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986),
  ch. 4, §1 and Thm. 2.7.
- D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*, 3rd ed., Springer (1999), ch.
  III, §1 and §3.
