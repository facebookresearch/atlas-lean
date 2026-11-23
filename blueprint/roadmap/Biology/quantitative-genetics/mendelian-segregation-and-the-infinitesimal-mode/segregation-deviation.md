# Offspring segregation deviation

For a measure `P` on the sample space, the offspring **segregation deviation** at `M` loci is
the function `R_M(ω) = ∑_{l < M} a_l (X_l(ω) - ∫ X_l dP)`, where `X_l` is the offspring's allele
count at locus `l` (a Mendelian draw given the parents) and `a_l` is the additive effect of the
locus. When `P` is a probability measure, `∫ X_l dP` is the mean `E X_l`; the integral is `0`
when `X_l` is not integrable. For `M = 0` the sum is empty and `R_0 = 0`.
