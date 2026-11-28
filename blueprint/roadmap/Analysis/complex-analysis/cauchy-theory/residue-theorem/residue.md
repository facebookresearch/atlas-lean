# Residue of a function at a point

The residue `Res_{z=a} f(z)` of `f` at `a`: the limit, as the radius `r` decreases to `0`, of
the normalized circle integral `(2πi)⁻¹ ∮_{|z-a|=r} f(z) dz`.

If `f` is holomorphic on a punctured neighbourhood of `a`, this integral is constant for all small
`r`, and `Complex.residue_eq_circleIntegral` shows that the residue equals it on every circle about
`a` whose closed disc lies in a set on which `f` is holomorphic away from `a`. For other `f` the
value carries no meaning.

The codomain must be complete: the circle integral is a Bochner integral, which is defined to be `0`
when the codomain is incomplete, so without completeness the limit would be `0` for every `f`. That
is a convention of the integral, not a property of circle integrals: around the unit circle, `v/z`
integrates to `2πi v` in the complete line spanned by `v`.
