# Fick's first law

**Fick's first law** in one dimension with constant diffusivity `D`: the flux of the
concentration field `c` (position, then time) at `(x, t)` is `J = -D ∂ₓc(x, t)`. The derivative
is Mathlib's `deriv`, which is `0` where `c (·) t` is not differentiable at `x`, so results about
`fickFlux` assume that differentiability separately.
