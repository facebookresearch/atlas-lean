# Maxwell–Boltzmann speed distribution

Maxwell–Boltzmann speed density (model input), for the gas constant `R`, absolute temperature `T`,
molar mass `M` and speed `v`:
`4 * π * (M / (2 * π * R * T)) ^ (3 / 2) * v ^ 2 * exp (-(M * v ^ 2) / (2 * R * T))`. The density is
meaningful for `R, T, M > 0`. It is defined for all real `R`, `T` and `M`: it is `0` for `R T = 0`,
by the convention `x / 0 = 0`, and for `M / (R T) < 0`, since `x ^ (3 / 2) = 0` for `x < 0`.
