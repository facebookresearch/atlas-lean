# Green's function of the sealed cable

For real numbers `τ`, `ℓ`, `L` and `x₀`, the Green's function of the sealed cable is the
[infinite expansion](cable-series.md) with the [point-charge coefficients](green-coeff.md) of `x₀`:

`G(t, x; x₀) = e^(-t/τ) / L + (2 / L) ∑_{n ≥ 1} e^(-k_n t) cos (n π x₀ / L) cos (n π x / L)`,

with `k_n` the [rate](decay-rate.md) of the `n`-th mode, the whole series over `n ≥ 0` being taken
with the convention that a non-summable series has sum `0`. With the convention `u / 0 = 0`, every
coefficient is `0` when `L = 0`, so `G ≡ 0` there. The solution, sealed-end, continuity,
coefficient, total-charge, superposition, semigroup and decay results about `G` assume `τ > 0`,
`ℓ ≠ 0` and `L ≠ 0`; its symmetries (reciprocity, evenness and periodicity in the source, sign under
`L ↦ -L`) hold for all real inputs.

For `τ > 0`, `ℓ ≠ 0`, `L > 0` and `x₀ ∈ [0, L]`, it is the potential at position `x ∈ [0, L]` and
time `t > 0` after a unit charge is injected at `x₀` at time `0` (an instantaneous, spatially
localized synaptic input). Outside that range it is an algebraic extension, not the response to a
point charge at `x₀`: for every `L` it is even and `2L`-periodic in `x₀`
([even](sealed-green-neg-source.md), [periodic](sealed-green-add-two-mul-source.md)), so a source
outside `[0, L]` gives the kernel of its image inside, and replacing `L` by `-L` negates it
([sign](sealed-green-neg-length.md)).
