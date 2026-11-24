# Offspring segregation deviation

For a measure `P` on the sample space, real numbers `a_l` and real functions `X_l`, the offspring
**segregation deviation** at `M` loci is the function
`R_M(ω) = ∑_{l < M} a_l (X_l(ω) - ∫ X_l dP)`. In the intended use `X_l` is the offspring's allele
count at locus `l` (a Mendelian draw given the parents) and `a_l` is the additive effect of the
locus, but the definition assumes no range, law, probability measure or integrability. When `P`
is a probability measure and `X_l` is integrable, `∫ X_l dP` is the mean `E X_l`; when `X_l` is
not integrable the integral is `0` by convention. For `M = 0` the sum is empty and `R_0 = 0`.
