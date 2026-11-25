# Covariance of unphased diploid genotypes

For real gamete frequencies $x : \{0, 1\}^2 \to \mathbb{R}$ at two biallelic loci, the genotype covariance is (Loh et al. 2013, Eq. 1)

$$z(x) = \sum_{g, h} x_g x_h (g_1 + h_1)(g_2 + h_2) - \Bigl(\sum_{g, h} x_g x_h (g_1 + h_1)\Bigr)\Bigl(\sum_{g, h} x_g x_h (g_2 + h_2)\Bigr),$$

the sums running over gametes $g, h \in \{0, 1\}^2$: for a probability vector $x$ (nonnegative frequencies summing to one), it is the covariance of the unphased genotypes $g_1 + h_1$ and $g_2 + h_2 \in \{0, 1, 2\}$ of an individual made of two gametes drawn independently from $x$.

## Sources

- P.-R. Loh, M. Lipson, N. Patterson, P. Moorjani, J. K. Pickrell, D. Reich, B. Berger, *Inferring admixture histories of human populations using linkage disequilibrium*, Genetics 193 (2013), 1233–1254.
