# Psi mul jacobian eq div

`psi * J(psi, q)` is a divergence: with `q_xy` the mixed partial of
`q`, the flux `(psi^2 / 2 * q_y, -psi^2 / 2 * q_x)` has divergence
`(psi * psi_x * q_y + psi^2 / 2 * q_xy) +
(-(psi * psi_y * q_x) - psi^2 / 2 * q_xy)`, which is
`psi * J(psi, q)`.
