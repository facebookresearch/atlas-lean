# Converting a dimensioned force vector there and back returns it

For unit choices `u₁`, `u₂` and a dimension `d`, let `s_d(u₁, u₂) > 0` be the factor that converts a
coordinate of dimension `d` from units `u₁` to units `u₂`. For all unit choices `u₁`, `u₂` and every
force vector `F` (components indexed by a set `ι`, dimension `d = M L T⁻²`), multiplying the
components of `F` by `s_d(u₁, u₂)` and then by `s_d(u₂, u₁)` and tagging the result as a force gives
`F` back.

Here `M`, `L` and `T` denote the mass, length and time dimensions.
