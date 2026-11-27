# Reweighting a carrier-free variant leaves the SKAT statistic unchanged

If the genotype column of variant `j` is zero, `Gᵢⱼ = 0` for every individual `i`, then replacing
its weight `wⱼ` by any real number `c` does not change the [SKAT statistic](skat-q.md): `Q(y)` is
unchanged for every phenotype `y`, every real `n × q` covariate matrix `X` and every real `n × n`
matrix `V`.
