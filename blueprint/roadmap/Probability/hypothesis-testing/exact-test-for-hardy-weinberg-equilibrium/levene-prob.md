# Levene's exact Hardy–Weinberg probability

Levene's conditional probability of `h` heterozygotes among `N` diploid individuals given
`nA` copies of allele `A` (and `nB = 2N - nA` of `B`) under Hardy–Weinberg equilibrium:
`N! nA! nB! 2^h / (nAA! h! nBB! (2N)!)` with `nAA = (nA - h) / 2`, `nBB = (nB - h) / 2`, when
`h ≤ nA`, `h ≤ nB` and `nA - h` is even, and `0` otherwise. The parameter domain is
`nA ≤ 2N`; for `nA > 2N` the value is `0`.
