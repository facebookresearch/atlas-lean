# Resultant force of the Winkler contact pressure

For a subgrade modulus `k_s`, a uniform settlement `a`, a small rotation `b` and a footing width
`B`, all real, the resultant force per unit out-of-plane length of the affine contact pressure
`p(x) = k_s (a + b x)`, with `x` the lateral coordinate from the footing centre, is the oriented
integral `F = ∫_{-B/2}^{B/2} k_s (a + b x) dx`. Units: `k_s` is a pressure per length (a force per
length cubed), `a`, `x` and `B` are lengths, `b` is an angle in radians, and `F` is a force per
length. The physical regime is `B > 0` and `k_s > 0`, a rigid footing in full Winkler contact,
integrated without a no-tension cutoff. For `B < 0` the lower bound `-B/2` exceeds the upper bound
`B/2`, and the oriented integral is minus the integral over `[B/2, -B/2]`.
