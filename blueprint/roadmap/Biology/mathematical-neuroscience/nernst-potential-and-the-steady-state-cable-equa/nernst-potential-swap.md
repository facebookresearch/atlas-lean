# Swapping inside and outside reverses the Nernst potential

For all real `R`, `T`, `z`, `F`, `c_in` and `c_out`, exchanging the inside and outside
concentrations reverses the sign of the [Nernst potential](nernst-potential.md):

`(R T / (z F)) log (c_in / c_out) = -(R T / (z F)) log (c_out / c_in)`.

No positivity is needed: `c_in / c_out` is the inverse of `c_out / c_in` and `log (1 / u) = -log u`
for every real `u`, including `u = 0` under the conventions `1 / 0 = 0` and `log 0 = 0`.
