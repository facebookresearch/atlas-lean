# Positive means with log-ratio orthogonal to 𝒮 give the same class laws

Let `N` be a [chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) with
finite species set `S` and any reaction set `ρ`, let `𝒮` be its
[stoichiometric subspace](../../../Dynamics/smooth-dynamics/stoichiometric-subspace.md), and let
`c, d ∈ ℝ^S` with `c_s > 0` and `d_s > 0` for every `s`. If the vector `(log d_s - log c_s)_s` is
orthogonal to `𝒮` for the dot product, then `c` and `d` give the same
[conditioned law](conditioned-law.md) on every [compatibility class](compat-class.md): for every
`x₀ ∈ ℕ^S`, `π_d(· | Γ) = π_c(· | Γ)` with `Γ = {x ∈ ℕ^S : x - x₀ ∈ 𝒮}`. Indeed
`π_d(x) / π_c(x) = π_d(x₀) / π_c(x₀)` for every `x ∈ Γ`, and
[weights proportional](conditioned-law-eq-of-forall-mem.md) on `Γ` with a nonzero factor give the
same law.
