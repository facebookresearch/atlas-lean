# Average natural indirect effect

**Average natural indirect effect** `NIE(x, x*; Y) = E(Y_{x*, Z_x}) - E(Y_{x*})` (P01, Definition 7,
eq. (20)), for treatment `t`, mediator `m`, outcome `y` read by `g`: the treatment stays at `x*`
while the mediator takes the value it would take under `x`. The `TE - NDE` convention (P14, fn. 13)
gives another quantity: `TE(x, x*; Y) - NDE(x, x*; Y)` equals `-NIE(x*, x; Y)` in every model (P01,
eq. (23)); it agrees with `NIE(x, x*; Y)` when the effects are additive, and in general not under
treatment-mediator interaction.
