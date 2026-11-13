# Covariance of local-ancestry indicators after pulse admixture

Pulse admixture: after `n` generations of random mating the local-ancestry indicators at
two loci with recombination fraction `r` have covariance `Cov(I_x, I_y) = α (1 - α) (1 - r)^n`
(for every real `α`, `r`; the biological domain is `0 ≤ α ≤ 1`, `0 ≤ r ≤ 1/2`). The
ancestry labels obey the two-locus random-mating recursion of `Linkage.recombine`
(Chakraborty and Weiss 1988).
