# Identification of the NIE by the mediation formula

**The mediation formula for the NIE** (P01, Theorem 4, eqs. (25)-(26); P14, Corollary 1, eq. (14b)).
Let the treatment `X` (node `t`) and the mediator `Z` (node `m`) be distinct nodes of a finite
recursive structural causal model with values in a finite set and independent noise laws, `Y` an
outcome node read through a real function `g`, `W` a set of nodes and `x`, `x*` two treatment
values. Assume, as independences under the noise law of the counterfactuals `Y_{x*z}` (the outcome
under `do(X = x*, Z = z)`) and `Z_{x'}` (the mediator under `do(X = x')`) and the factual `X`, `Z`,
`W`, for every mediator value `z` and for `x'` in `{x, x*}`:

- `Y_{x*z} ⫫ X | W`, H1 at `x*` only;
- `Y_{x*z} ⫫ Z | X, W`, H2 at `x*` only;
- `Z_{x'} ⫫ X | W`, H3 at both values;
- `Y_{x*z} ⫫ Z_{x'} | W`, the cross-world condition (P01, eq. (25)) at both values;

and positivity on the support: `P(W = w) > 0` implies `P(X = x, W = w) > 0` and
`P(X = x*, W = w) > 0`, and `P(X = x, Z = z, W = w) > 0` implies `P(X = x*, Z = z, W = w) > 0`. Then

`NIE(x, x*; Y) = ∑_{w,z} E(g(Y) | x*, z, w) [P(z | x, w) - P(z | x*, w)] P(w)`.

Under these positivity conditions, every term with a nonzero factor
`[P(z | x, w) - P(z | x*, w)] P(w)` conditions only on events of positive probability, so the
formula's convention for events of weight `0` does not enter. No premise that `W` is unaffected by
the treatment is needed.
