# Reading Celsius as kelvin underestimates the Boltzmann factor

For `E > 0`, an energy divided by `kB` and so given in kelvin, and a positive Celsius reading `t`,
reading `t` as `t` kelvin gives a smaller Boltzmann factor than converting it correctly to
`t + 273.15` kelvin: `exp (-E / t) < exp (-E / (t + 273.15))`.
