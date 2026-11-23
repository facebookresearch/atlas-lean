# Energy flux divergence

Energy-density identity in the flux `psi_t * grad psi` form: with
`e_t = psi_x * psi_xt + psi_y * psi_yt + psi * psi_t / Ld^2` the time
derivative of the energy density `0.5 * (|grad psi|^2 + psi^2 / Ld^2)`,
and `div (psi_t * grad psi) = psi_t * (psi_xx + psi_yy) + psi_xt * psi_x +
psi_yt * psi_y`, one has
`e_t = div (psi_t * grad psi) - psi_t * ((psi_xx + psi_yy) - psi / Ld^2)`,
that is `e_t = div - psi_t * q + beta * y * psi_t`. The residual is not a
divergence, and the channel boundary conditions do not remove
`beta * y * psi_t`, so this form alone does not give energy conservation;
`energy_flux_divergence_of_qg` is the conservation identity.
