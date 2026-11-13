# Mb Speed

Maxwell-Boltzmann speed density (CH08.1, model input), for the gas constant `R`, absolute
temperature `T`, molar mass `M` and speed `v`:
`4 * π * (M / (2 * π * R * T)) ^ (3 / 2) * v ^ 2 * exp (-(M * v ^ 2) / (2 * R * T))`.
Mathlib, Physlib and ATLAS `main` provide no Maxwell-Boltzmann speed density to reuse.
