# The mediation formula

Let `μ` be a probability measure on `Ω`; let the
exposure `X : Ω → 𝒳`, the covariates `Z : Ω → 𝒵` and the potential mediators `M(x) : Ω → ℳ` be
measurable with finite value types having measurable singletons; and let the potential outcomes
`Y(x, m) : Ω → ℝ` be measurable and bounded (`|Y(x, m)| ≤ C`). Assume, for all `x, x', m, z`:
* positivity: `P(X = x, M = m, Z = z) > 0`;
* no exposure–outcome confounding: `Y(x, m)` is independent of `X` given `Z = z`;
* no mediator–outcome confounding: `Y(x, m)` is independent of `M(x)` given `X = x, Z = z`;
* no exposure–mediator confounding: `M(x)` is independent of `X` given `Z = z`;
* no exposure-induced mediator–outcome confounding: `Y(x, m)` is independent of `M(x')` given
  `Z = z`.

Then for all `x₀, x₁`, with `P(z) = μ(Z = z)`, the natural direct effect (NDE) and the
total-minus-direct indirect effect (`NIE = TE - NDE`, holding exposure at `x₁` rather than at
`x₀` as in Pearl 2001's `E[Y(x₀, M(x₁))] - E[Y(x₀, M(x₀))]`) satisfy
`E[Y(x₁, M(x₀))] - E[Y(x₀, M(x₀))] = ∑_{z, m} (E[Y | x₁, m, z] - E[Y | x₀, m, z]) P(m | x₀, z) P(z)`
and
`E[Y(x₁, M(x₁))] - E[Y(x₁, M(x₀))] = ∑_{z, m} E[Y | x₁, m, z] (P(m | x₁, z) - P(m | x₀, z)) P(z)`.

## Sources

- J. Pearl, "Direct and indirect effects", Proc. 17th Conf. Uncertainty in Artificial Intelligence (2001) 411–420 (arXiv:1301.2300); T. J. VanderWeele and S. Vansteelandt, "Conceptual issues concerning mediation, interventions and composition", Stat. Interface 2 (2009) 457–468.
