# Generator of the Wright–Fisher diffusion with selection and mutation

For real numbers `α`, `θ₁`, `θ₂` and `x` and a real function `f`, let

`(L f)(x) = x (1 - x) / 2 · D(Df)(x) + (α x (1 - x) + (θ₁ (1 - x) - θ₂ x) / 2) · Df(x)`,

where, for a real function `g`, `Dg(x)` is the derivative of `g` at `x` where it exists and `0`
elsewhere; the second-order term applies `D` twice, so it can be nonzero where `f` has no classical
second derivative. The intended domain is `x ∈ [0, 1]`, `θ₁, θ₂ ≥ 0` and twice differentiable `f`:
there `Df = f'`, `D(Df) = f''`, and `L f` is the backward generator of the Wright–Fisher diffusion
with genic selection and two-way mutation, applied to `f`, with time in units of `2N` generations,
scaled selection coefficient `α = 2Ns` and scaled mutation rates `θ₁ = 4N u₁` towards the allele
and `θ₂ = 4N u₂` away from it.
