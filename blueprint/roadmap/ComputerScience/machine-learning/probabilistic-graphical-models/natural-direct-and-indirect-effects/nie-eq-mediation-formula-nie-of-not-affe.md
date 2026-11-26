# Identification of the NIE with nondescendant covariates

The mediation formula for the natural indirect effect with covariates that are nondescendants of the
treatment and of the mediator, as P01, Theorem 4, takes them. Let the treatment `X` (node `t`) and
the mediator `Z` (node `m`) be distinct nodes of a finite recursive structural causal model with
values in a finite set and independent noise laws, `Y` an outcome node read through a real function
`g`, `x`, `x*` two treatment values, and `W` a set of nodes inside a set `S` of nodes that contains
the parents of each of its members and contains neither `t` nor `m`: no member of `W` is a
descendant of the treatment or of the mediator, a premise stronger than P14's A-1, which excludes
only descendants of the treatment. Assume, under the noise law, for every mediator value `z`,
`Y_{x*z} ⫫ X | W` (H1 at `x*`) and `Y_{x*z} ⫫ Z | X, W` (H2 at `x*`), and for `x'` in `{x, x*}`,
`Z_{x'} ⫫ X | W` (H3 at both values) and `Y_{x*z} ⫫ Z_{x'} | W` (the cross-world condition at both
values), and positivity: `P(W = w) > 0` implies `P(X = x, W = w) > 0` and `P(X = x*, W = w) > 0`,
and `P(X = x, Z = z, W = w) > 0` implies `P(X = x*, Z = z, W = w) > 0`. Then

`NIE(x, x*; Y) = ∑_{w,z} E(g(Y) | x*, z, w) [P(z | x, w) - P(z | x*, w)] P(w)`.

Under these positivity conditions, every term with a nonzero factor
`[P(z | x, w) - P(z | x*, w)] P(w)` conditions only on events of positive probability, so the
formula's convention for events of weight `0` does not enter. The conclusion follows from the
independences and positivity alone.
