# Local upwind update of a cell

For viscosities `μo` and `μw`, a CFL number `ν`, a normalized saturation `a` of a cell and the
normalized saturation `b` of its left (upwind) neighbour (any real numbers), the local upwind
update is `a - ν * (f(a) - f(b))`, where `f` is the [fractional flow](frac-flow.md) with
viscosities `μo` and `μw`.
