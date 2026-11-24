# Pressure Force

The outward-normal force component `F = -p A` of a
uniform pressure `p` on a plane area `A > 0`: the negated
`WithDim` product, cast to `forceDim` by
`stressDim_mul_area`. The sign is the tension-positive
convention of `PhyslibExt.Units.EngineeringFrames`:
pressure is the negative of tension-positive normal
stress, so a positive pressure pushes against the
outward unit normal.
