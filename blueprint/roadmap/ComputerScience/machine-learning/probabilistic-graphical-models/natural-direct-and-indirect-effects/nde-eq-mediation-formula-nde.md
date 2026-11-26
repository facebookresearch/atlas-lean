# Identification of the NDE by the mediation formula

**The mediation formula** (P01, Theorem 2 with eq. (17); P14, Corollary 1, eq. (14a)). Let the
treatment `X` (node `t`) and the mediator `Z` (node `m`) be distinct nodes of a finite recursive
structural causal model with values in a finite set and independent noise laws, `Y` an outcome node
read through a real function `g`, `W` a set of nodes and `x`, `x*` two treatment values. Assume, for
`x'` in `{x, x*}` and every mediator value `z`, the four no-confounding conditions, independences
under the noise law of the counterfactuals `Y_{x'z}` (the outcome under `do(X = x', Z = z)`) and
`Z_{x*}` (the mediator under `do(X = x*)`) and the factual `X`, `Z`, `W`:

- (H1) `Y_{x'z} ⫫ X | W`, no treatment-outcome confounding;
- (H2) `Y_{x'z} ⫫ Z | X, W`, no mediator-outcome confounding;
- (H3) `Z_{x*} ⫫ X | W`, no treatment-mediator confounding;
- (H4) `Y_{x'z} ⫫ Z_{x*} | W`, the cross-world condition (P01, eq. (7));

and positivity on the support: `P(W = w) > 0` implies `P(X = x*, W = w) > 0`, and
`P(X = x*, Z = z, W = w) > 0` implies `P(X = x, Z = z, W = w) > 0`. Then

`NDE(x, x*; Y) = ∑_{w,z} [E(g(Y) | x, z, w) - E(g(Y) | x*, z, w)] P(z | x*, w) P(w)`.

Under these positivity conditions, every term with a nonzero factor `P(z | x*, w) P(w)` conditions
only on events of positive probability, so the formula's convention for events of weight `0` does
not enter. No premise that `W` is unaffected by the treatment is needed. Neither source states
positivity, and the formula fails without it: a deterministic model whose treatment never takes the
value `x` satisfies H1-H4 and the first positivity condition, yet its NDE is `1` while the formula
is `0`, since the event `X = x, Z = z` has probability zero and the weighted mean over it is `0` by
convention.
