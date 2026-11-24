# Lumped meanline port of a rotor control volume

A lumped (meanline) port of a rotor control volume is the flow state at one representative point,
with the port area. It consists of real numbers:

- the density `ρ` and the port area `A`, with `ρ ≥ 0` and `A ≥ 0`;
- the static pressure `p`, of either sign;
- the azimuth `φ` (in radians), the radius `r`, with `r ≥ 0`, and the axial station `z` of the
  representative point;
- the components `(c_r, c_θ, c_z)` of the inertial fluid velocity in the
  [local cylindrical frame](cyl-frame.md) at azimuth `φ`;
- the meridional components `(n_r, 0, n_z)` of the outward unit normal in that frame, with
  `n_r² + n_z² = 1`.

No port surface is modelled. The swirl `c_θ` is the inertial tangential velocity, positive along
`e_θ`, the sense of increasing azimuth (counterclockwise seen from the tip of `e₃`). The condition
`r ≥ 0` puts the representative point on the radial ray `e_r` of its azimuth, and `r` is the port's
effective moment radius: the radius for which `ṁ r c_θ` is its angular-momentum outflow, the
[lumped axial angular-momentum flux](axial-moment-flux.md).
