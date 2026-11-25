# Covariance of allele counts within a gamete

For real gamete frequencies $x : \{0, 1\}^2 \to \mathbb{R}$ at two biallelic loci (a gamete $g = (g_1, g_2)$ records its alleles at the two loci), the allele covariance is

$$\mathrm{Cov}(x) = \sum_{g} x_g\, g_1 g_2 - \Bigl(\sum_{g} x_g\, g_1\Bigr)\Bigl(\sum_{g} x_g\, g_2\Bigr):$$

for a probability vector $x$ (nonnegative frequencies summing to one), it is the covariance of the [allele counts](allele-count.md) at the two loci of one gamete drawn from $x$.
