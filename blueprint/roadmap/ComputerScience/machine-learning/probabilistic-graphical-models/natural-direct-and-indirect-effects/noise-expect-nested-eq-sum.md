# Adjustment formula for the nested counterfactual mean

**P01, Theorem 1, eqs. (9)-(10)**. Let `X` (node `t`) and `Z` (node `m`) be nodes of a finite
recursive structural causal model with values in a finite set and independent noise laws, `Y` an
outcome node read through a real function `g`, `W` a set of nodes and `x`, `x'` two treatment
values. If the cross-world independence `Y_{xz} ⫫ Z_{x'} | W` holds under the noise law for every
mediator value `z` (P01, eq. (7)), the mean of the nested counterfactual decomposes over the factual
covariates:

`E(g(Y_{x, Z_{x'}})) = ∑_{w,z} E(g(Y_{xz}) | w) P(Z_{x'} = z | w) P(w)`,

where `| w` conditions on `W = w`. The terms with `P(w) = 0` vanish, and in the others the
conditioning event `W = w` has positive probability. No positivity is needed.
