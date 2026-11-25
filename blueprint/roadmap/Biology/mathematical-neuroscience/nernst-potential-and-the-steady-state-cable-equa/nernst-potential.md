# Nernst potential of an ion species

For real numbers `R`, `T`, `z`, `F`, `c_in` and `c_out`, the Nernst potential is

`E = (R T / (z F)) log (c_out / c_in)`,

with gas constant `R`, absolute temperature `T`, ion valence `z`, Faraday constant `F`, inside
concentration `c_in` and outside concentration `c_out`.

The formula is defined for all real inputs, with the conventions `u / 0 = 0`, `log 0 = 0` and
`log u = log |u|` for `u < 0`. So `E = 0` when `z F = 0`, when `c_in = 0` or when `c_out = 0`, and
for concentrations of opposite signs the logarithm is that of `|c_out / c_in|`.

In the model `R`, `T`, `F`, `c_in` and `c_out` are positive and `z` is a nonzero valence. Then `E`
is the inside-minus-outside membrane voltage at which the species is in electrochemical
equilibrium: the electrochemical potentials inside and outside agree exactly at this voltage
([equal electrochemical potentials](electrochemical-potential-eq-iff.md)), and a zero
Nernst–Planck flux across the membrane forces it
([zero flux](sub-eq-nernst-potential-of-flux-eq-zero.md)).
