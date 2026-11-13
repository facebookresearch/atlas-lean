# Wright–Fisher generator with two-way mutation

The backward generator of the Wright–Fisher diffusion with two-way mutation, time in units of
`2N` generations and scaled mutation rates `θ₁ = 4N u₁` (towards the allele) and `θ₂ = 4N u₂`
(away from it): `(L f)(x) = x (1 - x) / 2 · f''(x) + (θ₁ (1 - x) - θ₂ x) / 2 · f'(x)`.
