# Point Mass gradient inward

Outside the origin, the gradient of the point-mass potential
`Φ(x) = -G*M/‖x‖` is `(G*M/‖x‖^3) • x` (`hasGradientAt_pointMass_potential`,
stated here through `toDual`), so the acceleration `-∇Φ` is
`-(G*M/‖x‖^3) • x`; for `G, M > 0` it points inward: its inner product with
the outward position vector `x` is negative. This is the full vector
gradient, not only the radial derivative.
