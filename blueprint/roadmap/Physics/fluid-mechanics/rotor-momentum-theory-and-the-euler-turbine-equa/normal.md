# Outward unit normal n_r e_r + n_z e₃ at a port

For a [port](rotor-port.md) of azimuth `φ` with the normal components `(n_r, 0, n_z)`, the outward
normal at its representative point is `n = n_r e_r + n_z e₃ = (n_r cos φ, n_r sin φ, n_z)`, with
`e_r` the radial vector of the [local cylindrical frame](cyl-frame.md). It lies in the meridional
plane of the point, and it is a unit vector because the port has `n_r² + n_z² = 1`. By convention it
points out of the control volume.
