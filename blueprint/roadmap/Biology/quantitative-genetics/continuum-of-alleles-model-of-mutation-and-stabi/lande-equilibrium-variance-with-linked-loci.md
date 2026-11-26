# Lande's equilibrium genetic variance under mutation and stabilizing selection with linked loci

A character $z = X + e$ is determined by $n$ diploid loci with additive allelic effects, $X = \sum_{i=1}^n (x_i + x_i')$, plus an environmental deviation $e \sim N(0, \sigma_e^2)$. Fitness is Gaussian with optimum $\theta$ and width $\omega^2$,

$$w(z) = \exp\Bigl(-\frac{(z - \theta)^2}{2\omega^2}\Bigr).$$

Each generation, an allele at locus $i$ mutates with probability $\mu_i$, and its effect changes by a mean-zero increment of variance $m_i^2$. Assume random mating, infinite population size, arbitrary recombination fractions $r_{ij}$, and a multivariate normal distribution of allelic effects in gametes (justified when mutational changes are small, $m_i^2 \ll$ the per-locus allelic variance). Let $C_{ij}$ be the gametic covariance of effects at loci $i$, $j$, let $B_i = \sum_j C_{ij}$, and let $\sigma_g^2 = 2\sum_i B_i$ be the expressed (additive genetic) variance. Then:

1. **Mean.** The mean phenotype $\bar z$ moves towards the optimum as

$$\bar z(t+1) - \theta = \frac{\omega^2 + \sigma_e^2}{\omega^2 + \sigma_e^2 + \sigma_g^2(t)}\,\bigl(\bar z(t) - \theta\bigr),$$

the response of the mean being heritability times the selection differential. The mean effects at individual loci have no stable equilibrium: only their sum is constrained.
2. **Equilibrium variance.** The covariance recursion has a unique admissible equilibrium, with

$$\hat B_i^2 = \mu_i m_i^2\,\bigl(\omega^2 + \sigma_e^2 + \hat\sigma_g^2\bigr), \qquad \hat\sigma_g^2 = 2\sum_{i=1}^n \hat B_i = 2\sqrt{\omega^2 + \sigma_e^2 + \hat\sigma_g^2}\;\sum_{i=1}^n \sqrt{\mu_i m_i^2}.$$

So the expressed genetic variance does not depend on the recombination fractions. With weak selection ($\omega^2 + \sigma_e^2 \gg \hat\sigma_g^2$), $\hat\sigma_g^2 \approx 2\sum_i \sqrt{\mu_i m_i^2 (\omega^2 + \sigma_e^2)}$, Kimura's one-locus formula summed over loci.
3. **Hidden variation.** Linkage changes only the between-locus covariances, which are negative, the "hidden" variation that tight linkage stores. The approximation breaks down as $r_{ij} \to 0$, where saturation effects bound the per-locus variances.

## Depends on

- [Gaussian stabilizing fitness](fitness.md)
- [Mutational variance](mut-var.md)
- [Equilibrium of the continuum-of-alleles model](stationary-law-of-the-continuum-of-alleles-model.md)

## Proof depends on

- [Gaussian stabilizing fitness](fitness.md)
- [Mutational variance](mut-var.md)
- [Equilibrium of the continuum-of-alleles model](stationary-law-of-the-continuum-of-alleles-model.md)

## Expansion

Gaussian selection on a normal phenotype keeps the zygotic distribution of allelic effects multivariate normal and shrinks its covariance by a rank-one update. Recombination reshuffles the between-locus covariances without touching the per-locus sums that make up expressed variance. Mutation adds $\mu_i m_i^2$ to each diagonal entry. At equilibrium, the variance selection removes from the expressed component, about $B_i^2/(\omega^2 + \sigma_e^2 + \sigma_g^2)$ at locus $i$, must equal the mutational input $\mu_i m_i^2$. This balance involves only the expressed quantities, so it holds whatever the linkage map; recombination only moves variance between the expressed and hidden parts.

## Sources

- R. Lande, *The maintenance of genetic variability by mutation in a polygenic character with linked loci*, Genet. Res. 26 (1975), 221–235, <https://doi.org/10.1017/S0016672300016037>: Section 2 (assumptions), Section 3 (qualitative linkage-independence argument), Section 4, Eqs. (4) (fitness), (14) (mean dynamics), (20) and (21c) (equilibrium expressed variance), and the normality conditions (23)–(24).
