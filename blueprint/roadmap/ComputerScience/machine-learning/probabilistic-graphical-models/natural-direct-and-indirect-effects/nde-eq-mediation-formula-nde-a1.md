# Identification of the NDE under A-1

The mediation formula for the natural direct effect (P14, Corollary 1, eq. (14a); P01, Theorem 2)
under P14's assumption **A-1** as published, covariates unaffected by the treatment. Let the
treatment `X` (node `t`) and the mediator `Z` (node `m`) be distinct nodes of a finite recursive
structural causal model with values in a finite set and independent noise laws, `Y` an outcome node
read through a real function `g`, `W` a set of nodes and `x`, `x*` two treatment values. Assume A-1:
for every node `i` of `W`, every treatment value `a` and every noise value `u`, the value of node
`i` under `do(X = a)` at `u` is its factual value at `u`; nothing is assumed about the mediator.
Assume also, under the noise law, for `x'` in `{x, x*}` and every mediator value `z`, (H1)
`Y_{x'z} ⫫ X | W`, (H2) `Y_{x'z} ⫫ Z | X, W`, (H3) `Z_{x*} ⫫ X | W` and (H4) `Y_{x'z} ⫫ Z_{x*} | W`,
and positivity: `P(W = w) > 0` implies `P(X = x*, W = w) > 0`, and `P(X = x*, Z = z, W = w) > 0`
implies `P(X = x, Z = z, W = w) > 0`. Then

`NDE(x, x*; Y) = ∑_{w,z} [E(g(Y) | x, z, w) - E(g(Y) | x*, z, w)] P(z | x*, w) P(w)`.

Under these positivity conditions, every term with a nonzero factor `P(z | x*, w) P(w)` conditions
only on events of positive probability, so the formula's convention for events of weight `0` does
not enter. The conclusion follows from H1-H4 and positivity alone; A-1 completes the published
hypothesis set.
