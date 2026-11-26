# Identification of the NDE without covariates

**The mediation formula without covariates** (P01, eq. (17); P14, eq. (16)). Let the treatment `X`
(node `t`) and the mediator `Z` (node `m`) be distinct nodes of a finite recursive structural causal
model with values in a finite set and independent noise laws, `Y` an outcome node read through a
real function `g` and `x`, `x*` two treatment values. Assume H1-H4 with no covariates, for `x'` in
`{x, x*}` and every mediator value `z`: `Y_{x'z} ⫫ X`, `Y_{x'z} ⫫ Z | X`, `Z_{x*} ⫫ X` and
`Y_{x'z} ⫫ Z_{x*}` under the noise law; and positivity: `P(X = x*) > 0`, and `P(X = x*, Z = z) > 0`
implies `P(X = x, Z = z) > 0`. Then

`NDE(x, x*; Y) = ∑_z [E(g(Y) | X = x, Z = z) - E(g(Y) | X = x*, Z = z)] P(Z = z | X = x*)`.

Under these positivity conditions, every term with a nonzero factor `P(Z = z | X = x*)` conditions
only on events of positive probability, so the formula's convention for events of weight `0` does
not enter.
