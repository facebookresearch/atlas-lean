# SEIR chain paths are chain paths of the mass-action system

Let `β`, `σ`, `γ`, `μ` be nonnegative, and let `(S, E, I, R)` be a [chain path](is-chain-path.md) at
scale `N` driven by functions `y_c` whose birth path `y_birth` is nondecreasing (as the path of a
Poisson process is, almost surely). Then the [count vector path](to-path.md)
`Z(t) = (S, E, I, R)(max(t, 0))` is a chain path of the
[stochastic mass-action system](chain-crn.md) at system size `N`, driven by the same `y_c`:

- each coordinate of `Z` is measurable;
- for every channel `c` and every real `t`, the propensity `x ↦ λ^N_c(Z(x))` is integrable between
  `0` and `t`;
- for every `t ≥ 0`, `Z(t) = Z(0) + ∑_c y_c(Λ_c(t)) (prod(c) - src(c))` as real vectors, where
  `Λ_c(t) = max(∫₀ᵗ λ^N_c(Z(x)) dx, 0)`.

The propensities along `Z` are constant on `(-∞, 0]`. On `[0, t]` every count is at most
`S(0) + E(0) + I(0) + R(0) + y_birth(N μ t)`, by the [total bound](total-le.md) and the monotonicity
of `y_birth`, so the propensities are bounded there.
