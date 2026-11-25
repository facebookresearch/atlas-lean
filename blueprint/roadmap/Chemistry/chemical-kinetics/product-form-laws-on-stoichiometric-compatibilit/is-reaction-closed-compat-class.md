# Compatibility classes are reaction-closed

Let `N` be a [chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) with
species set `S` and reaction set `ρ`, not necessarily finite, and `𝒮` its
[stoichiometric subspace](../../../Dynamics/smooth-dynamics/stoichiometric-subspace.md). For every
state `x₀ ∈ ℕ^S`, the [compatibility class](compat-class.md) `{x ∈ ℕ^S : x - x₀ ∈ 𝒮}` is
[reaction-closed](is-reaction-closed.md): if `x` lies in it, then so does `x - src(r) + prod(r)` for
every reaction `r` with `src(r) ≤ x`, and so does `x - prod(r) + src(r)` for every `r` with
`prod(r) ≤ x`. Firing `r` adds the reaction vector `prod(r) - src(r)` to the state and unfiring
subtracts it, and that vector [lies in the subspace](reaction-vector-mem.md).
