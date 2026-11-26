# Identification of the NIE without covariates

**The NIE mediation formula without covariates** (P01, eq. (27); P14, eq. (17)). Let the treatment
`X` (node `t`) and the mediator `Z` (node `m`) be distinct nodes of a finite recursive structural
causal model with values in a finite set and independent noise laws, `Y` an outcome node read
through a real function `g` and `x`, `x*` two treatment values. Assume, under the noise law, for
every mediator value `z`, `Y_{x*z} ⫫ X` and `Y_{x*z} ⫫ Z | X`, and for `x'` in `{x, x*}`,
`Z_{x'} ⫫ X` and `Y_{x*z} ⫫ Z_{x'}`; and positivity: `P(X = x) > 0` and `P(X = x*) > 0`, and
`P(X = x, Z = z) > 0` implies `P(X = x*, Z = z) > 0`. Then

`NIE(x, x*; Y) = ∑_z E(g(Y) | X = x*, Z = z) [P(Z = z | X = x) - P(Z = z | X = x*)]`.

Under these positivity conditions, every term with a nonzero factor
`P(Z = z | X = x) - P(Z = z | X = x*)` conditions only on events of positive probability, so the
formula's convention for events of weight `0` does not enter.
