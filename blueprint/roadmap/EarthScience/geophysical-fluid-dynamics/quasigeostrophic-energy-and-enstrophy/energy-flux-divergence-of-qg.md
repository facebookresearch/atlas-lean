# Energy conservation identity

For a nonzero deformation radius
`Ld`, with `e_t` and `q_t = (psi_xxt + psi_yyt) - psi_t / Ld^2` as in
`energy_density_rate_eq`,
and the QG equation `q_t = -J(psi, q)`, the energy density satisfies
`e_t = div G` for
`G = (psi * psi_xt + psi^2 / 2 * q_y, psi * psi_yt - psi^2 / 2 * q_x)`,
whose divergence is written out on the right (`q_xy` is the mixed
partial of `q`). On the walls `psi = 0`, so `G_y = 0` there; with
`Lx`-periodic `x`, the channel integral of `div G` vanishes by the
divergence theorem, which is energy conservation.
