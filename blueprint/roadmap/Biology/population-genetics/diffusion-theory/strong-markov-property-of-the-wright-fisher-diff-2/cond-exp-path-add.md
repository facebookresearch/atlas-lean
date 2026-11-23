# Path Markov property with selection at a deterministic time

Let `κ = (κ_t)_{t ≥ 0}` be a family of Markov kernels on `[0, 1]` satisfying the Chapman–Kolmogorov
equations `κ_{s + t}(x, ·) = ∫ κ_t(y, ·) κ_s(x, dy)`, `μ` a finite measure on a measurable space
`Ω`, `(ℱ_t)_{t ≥ 0}` a filtration, `σ` a real number and `X` a
[Wright–Fisher diffusion with selection `σ`, Markov for `κ`](is-selection-markov.md), with respect
to `(ℱ_t)` and `μ`. Then for every time `s ≥ 0` and every bounded measurable `F` on the
[sample paths](../construction-of-the-neutral-wright-fisher-diffus/sample-path.md),

`μ[F((X_{s + u})_{u ≥ 0}) | ℱ_s] = ∫ F dP^κ_{X_s}` `μ`-almost everywhere,

where `P^κ_y` is the
[path measure](../../../../Probability/markov-chains/markov-processes-from-transition-semigroups/path-measure.md)
of `κ` from `y`. No Feller property is assumed.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986),
  ch. 4, §1.
- D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*, 3rd ed., Springer (1999), ch.
  III, §1.
