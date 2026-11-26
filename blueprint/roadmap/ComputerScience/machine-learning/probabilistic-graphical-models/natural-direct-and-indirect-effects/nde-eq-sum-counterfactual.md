# Counterfactual adjustment formula for the NDE

**P01, Theorem 1, eq. (8)** (counterfactual form). Let `X` (node `t`) and `Z` (node `m`) be nodes of
a finite recursive structural causal model with values in a finite set and independent noise laws,
`Y` an outcome node read through a real function `g`, `W` a set of nodes and `x`, `x*` two treatment
values. If the cross-world independence `Y_{x'z} ⫫ Z_{x*} | W` holds under the noise law for `x'` in
`{x, x*}` and every mediator value `z` (P01, eq. (7)), then

`NDE(x, x*; Y) = ∑_{w,z} [E(g(Y_{xz}) | w) - E(g(Y_{x*z}) | w)] P(Z_{x*} = z | w) P(w)`,

where `| w` conditions on the factual covariates `W = w`. The terms with `P(w) = 0` vanish, and in
the others the conditioning event `W = w` has positive probability.
