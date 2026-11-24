# Radiosity equations of a diffuse gray enclosure

For `σ`, emissivities `ε`, view factors `F` and temperatures `T` on a finite set of surfaces, a
radiosity field `J` solves the radiosity equations when, for every surface `i`,

`J_i = ε_i σ T_i⁴ + (1 - ε_i) ∑_j F_{ij} J_j`:

the radiosity is the emitted power per area plus the reflected fraction `1 - ε_i` of the
irradiation. In the physical reading `0 < ε_i ≤ 1`, the absorptivity is `ε_i` and the reflectivity
`1 - ε_i`.
