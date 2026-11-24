# The Gaussian solves the diffusion equation

For `D > 0`, `t > 0` and every real `M`
and `x`, `∂ₜ gauss = D ∂ₓₓ gauss` at `(x, t)`. This is `EarthScience.point_release_solves_adr`
with no drift and no reaction; the derivatives exist by `gauss_tderiv_value` and
`gauss_xxderiv_value`.
