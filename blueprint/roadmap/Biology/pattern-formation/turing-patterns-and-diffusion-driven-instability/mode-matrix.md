# Mode matrix of a linearized reaction-diffusion system

The mode matrix `J - k² D` governing the Fourier mode of wavenumber `k` of the linearized
system `w_t = D w_xx + J w`, where `J` is the Jacobian of the kinetics at the steady state
(convention: `J i j` is the partial derivative of the `i`-th reaction term with respect to the
`j`-th species, so `J = [[f_u, f_v], [g_u, g_v]]`).
