# Neg div mul deriv linear profile

Unrestricted algebraic identity behind the Brunt-Vaisala formula: for all
real `g, beta, rho0` (with Lean's total division),
`-(g / rho0) * deriv (fun z => rho0 - beta * z) z = g * beta / rho0`, since the
profile's gradient is `-beta` by `boussinesq_density_deriv`. It is the squared
Brunt-Vaisala frequency only in the physical domain `rho0 > 0`; see
`brunt_vaisala_from_gradient`.
