# Pmoebius

The affine reading `toAffine (g • z)` of the projective action of `g ∈ PGL(2, K₀)` on `z : K`.
When `g` sends `z` to `∞` (which happens only for `K₀`-rational `z`) the result is `0`, not a
point of the projective line, so `pmoebius` is the Möbius transformation only where the image is
finite: on the upper half plane (`coe_pmoebius_of_mem`), or for a representative of `g` whose
denominator does not vanish at `z` (`pmoebius_mk`).
