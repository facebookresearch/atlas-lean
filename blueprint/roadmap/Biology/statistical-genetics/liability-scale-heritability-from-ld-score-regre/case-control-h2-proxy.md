# Case-control heritability proxy with the population genetic variance

For a measure `μ` on `Ω`, real functions `L` and `G` on `Ω` (liability and genetic value), a real
threshold `t` and a real case fraction `P`, the case-control heritability proxy is

`h²_cc = Cov_cc(G, Y)² / (Var G · Var_cc Y)`,

where `Y = 1{L ≥ t}` is the [case indicator](case-ind.md), `Cov_cc` and `Var_cc` are taken under the
[case-control law](case-control.md) `μ_cc` with case fraction `P`, and `Var G` is the variance of
`G` under `μ`. With the convention `x / 0 = 0` it is `0` when `Var G = 0` or `Var_cc Y = 0`. It is
not the squared correlation of `G` and `Y` under the case-control law,
`Cov_cc(G, Y)² / (Var_cc G · Var_cc Y)`: ascertainment changes the variance of `G`, while the proxy
keeps its population variance. Under the Gaussian liability model the case-control factor of Lee et
al. (2011) recovers the liability-scale heritability from this proxy
([case-control conversion](h2-eq-cc-liability-factor-mul.md)).
