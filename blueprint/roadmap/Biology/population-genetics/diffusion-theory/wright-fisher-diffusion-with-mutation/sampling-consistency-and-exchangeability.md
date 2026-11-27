# Sampling consistency and exchangeability for diffusion samples

If allele frequencies $p = (p_1, \dots, p_K)$ have the Dirichlet law with parameters $\alpha_1, \dots, \alpha_K > 0$ and, given $p$, a sample of $n$ genes is multinomial with probabilities $p$, then the sample counts $x = (x_1, \dots, x_K)$ with $\sum_kx_k = n$ have the Dirichlet-multinomial law

$$P(x) = \frac{\Gamma(\alpha_0)\Gamma(n + 1)}{\Gamma(n + \alpha_0)}\prod_{k=1}^K\frac{\Gamma(x_k + \alpha_k)}{\Gamma(\alpha_k)\Gamma(x_k + 1)}, \qquad \alpha_0 = \sum_k\alpha_k$$

(Mosimann 1962, the compound multinomial distribution). The sequence of sampled types is, given $p$, independent and identically distributed, so its law is exchangeable, and the first $n - 1$ genes of a sample of $n$ form a sample of $n - 1$; both properties hold conditionally on $p$ and are preserved by mixing (derivation). In particular, a sample of $n$ genes from a population whose frequencies follow a stationary Dirichlet law of the diffusion is Dirichlet-multinomial with the parameters of that law.

## Depends on

- [Uniqueness and reversibility of the Dirichlet stationary law under parent-independent mutation](../../../../Biology/population-genetics/diffusion-theory/wright-fisher-diffusion-with-mutation/dirichlet-stationary-law-under-parent-independent-mutation.md)
- [Infinite-alleles limits of finite-allele diffusions](../../../../Biology/population-genetics/diffusion-theory/wright-fisher-diffusion-with-mutation/infinite-alleles-and-finite-allele-limits.md)
- [Dirichlet distribution](../../../../Probability/distributions/continuous/dirichlet-distribution/dirichlet-law/dirichlet-measure.md)

## Expansion

1. The Dirichlet-multinomial law, by integrating the multinomial probability against the Dirichlet density.
2. Exchangeability and consistency under subsampling of mixtures of independent identically distributed sequences.
3. The sample law from a stationary Dirichlet law of the diffusion, and its moments.
4. The marginal counts of one type as beta-binomial, by aggregating the other types.

## Sources

- J. E. Mosimann, On the compound multinomial distribution, the multivariate $\beta$-distribution, and correlations among proportions, Biometrika 49 (1962), 65–82.
