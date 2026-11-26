# Adjustment formula for the nested counterfactual mean

**P01, Theorem 1, eqs. (9)-(10)**. Let `X` (node `t`) and `Z` (node `m`) be nodes, `Y` an outcome
node read through a real function `g`, `W` a set of nodes and `x`, `x'` two treatment values. If the
cross-world independence `Y_{xz} ⫫ Z_{x'} | W` holds under the noise law for every mediator value
`z` (P01, eq. (7)), the mean of the nested counterfactual decomposes over the factual covariates:

`E(g(Y_{x, Z_{x'}})) = ∑_{w,z} E(g(Y_{xz}) | w) P(Z_{x'} = z | w) P(w)`,

where `| w` conditions on `W = w`, and a conditional mean or probability given an event of
probability zero is read as `0`. No positivity is needed.
