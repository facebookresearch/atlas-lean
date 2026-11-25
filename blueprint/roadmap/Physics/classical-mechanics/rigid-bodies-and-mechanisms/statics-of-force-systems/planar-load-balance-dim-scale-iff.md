# Planar balance does not depend on the choice of units

For unit choices `u₁`, `u₂` and a dimension `d`, let `s_d(u₁, u₂) > 0` be the factor that converts a
coordinate of dimension `d` from units `u₁` to units `u₂`. Let `x_i` (`i` in a finite index set) be
lever arms, plane vectors of dimension `L` (positions relative to the moment point, in one frame),
and `F_i` forces, plane vectors of dimension `M L T⁻²` in the same frame. With every lever arm
multiplied by the length factor `s_d(u₁, u₂)` (`d = L`) and every force by the force factor
`s_d(u₁, u₂)` (`d = M L T⁻²`), the converted system satisfies the force balance and the
[moment balance](planar-load-balance-iff.md) if and only if the original system does. The proof uses
that the conversion factors are positive.

Here `M`, `L` and `T` denote the mass, length and time dimensions.
