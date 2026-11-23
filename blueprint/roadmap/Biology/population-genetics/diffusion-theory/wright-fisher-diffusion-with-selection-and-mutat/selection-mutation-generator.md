# Generator of the Wright–Fisher diffusion with selection and mutation

For real numbers `α`, `θ₁`, `θ₂` and `x` and a real function `f`, let

`(L f)(x) = x (1 - x) / 2 · f''(x) + (α x (1 - x) + (θ₁ (1 - x) - θ₂ x) / 2) · f'(x)`,

where a derivative that does not exist is taken to be `0`; the only divisions are by the constant
`2`, so no division by `0` occurs. The intended domain is `x ∈ [0, 1]`, `θ₁, θ₂ ≥ 0` and twice
differentiable `f`: there `L f` is the backward generator of the Wright–Fisher diffusion with genic
selection and two-way mutation, applied to `f`, with time in units of `2N` generations, scaled
selection coefficient `α = 2Ns` and scaled mutation rates `θ₁ = 4N u₁` towards the allele and
`θ₂ = 4N u₂` away from it.
