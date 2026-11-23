# Brunt vaisala from gradient

Brunt-Vaisala frequency of the linear Boussinesq profile in the physical
domain `g > 0`, `rho0 > 0`: the squared frequency
`N^2 = -(g / rho0) * rho_z`, where `rho_z = deriv (fun z => rho0 - beta * z) z`
is the profile's vertical gradient at height `z`, equals `g * beta / rho0`, and
the stratification is stable (`N^2 > 0`), neutral (`N^2 = 0`), or unstable
(`N^2 < 0`) exactly when `beta > 0`, `beta = 0`, or `beta < 0`.
