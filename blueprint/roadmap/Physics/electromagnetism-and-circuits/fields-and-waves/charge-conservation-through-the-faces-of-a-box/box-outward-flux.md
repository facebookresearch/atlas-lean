# Outward flux of a current density through a box face

For `a, b ∈ ℝ³` the box is `[a, b] = {x ∈ ℝ³ : a_i ≤ x_i ≤ b_i for i = 0, 1, 2}`, with coordinate
axes indexed `0, 1, 2`. For a current density `J : ℝ³ → ℝ³`, the outward flux through face `f` is

`Φ_f = ∫_{R_f} s_f J_k(φ_f(y)) dy`,

the integral over the [parameter rectangle](box-face-domain.md) `R_f` of the
[outward-normal density](box-normal-density.md), with `k` the [normal axis](face-axis.md) of `f`,
`s_f` its [outward sign](face-sign.md) and `φ_f` its [embedding](box-face-embed.md); the integral is
with respect to Lebesgue measure on `ℝ²` and is `0` when the integrand is not integrable there. For
`a ≤ b` each face is a translate of a coordinate rectangle, so this is the surface integral of
`J · n` over the face, `n` the outward unit normal.
