# Flux divergence eq advective

Conservative and advective forms agree at a point: if the carrier
velocity satisfies the 1-D continuity equation `∂ₓU = 0` at `x`
(`HasDerivAt U 0 x`) and `c` and `cₓ` are differentiable at `x`, then
the divergence of the flux `J = U * c - D * cₓ` at `x` equals the
advective operator `U * cₓ - D * cₓₓ` at `x`.
