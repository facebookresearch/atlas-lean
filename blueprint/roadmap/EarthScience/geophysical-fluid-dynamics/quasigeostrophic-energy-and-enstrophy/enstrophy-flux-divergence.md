# Enstrophy flux divergence

Enstrophy flux divergence: for `q` with partials `q_x, q_y` and
`psi` with partials `psi_x, psi_y, psi_xy`, the flux
`F = (-psi_y * q^2 / 2, psi_x * q^2 / 2)` has divergence
`q * J(psi, q)`. Hence `d/dt (q^2 / 2) = -q * J(psi, q)` is in
divergence form: integrated over the channel it reduces to boundary
terms, which vanish for periodic-in-`x` and wall (`psi = 0`) conditions.
