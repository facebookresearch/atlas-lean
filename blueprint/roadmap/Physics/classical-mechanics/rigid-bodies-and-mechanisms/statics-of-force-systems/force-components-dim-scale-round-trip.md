# Converting force components there and back returns them

For unit choices `u₁`, `u₂` and a dimension `d`, let `s_d(u₁, u₂) > 0` be the factor that converts a
coordinate of dimension `d` from units `u₁` to units `u₂`. For all unit choices `u₁`, `u₂` and every
family `f` of real components (indexed by any set), `s_d(u₂, u₁) (s_d(u₁, u₂) f) = f` componentwise
for the force dimension `d = M L T⁻²`: converting force components from `u₁` to `u₂` and back
returns them.

Equivalently, for every force vector `F` (components indexed by a set `ι`), multiplying its
components by `s_d(u₁, u₂)` and then by `s_d(u₂, u₁)` and tagging the result as a force gives `F`
back.

Here `M`, `L` and `T` denote the mass, length and time dimensions.
