# Outbreak size distribution under negative-binomial offspring

**Setting.** A single imported case starts a Galton–Watson branching process in which every case independently causes a negative-binomial number of secondary cases with mean $R_0 > 0$ and dispersion $k > 0$ (probability generating function $(1 + R_0(1-s)/k)^{-k}$). Let $J \ge 1$ be the total number of cases ever caused by the introduction, including the index case.

**Distribution.** For $j = 1, 2, \dots$,

$$P(J = j) = \frac{\Gamma(kj + j - 1)}{\Gamma(kj)\,\Gamma(j+1)}\,\frac{(R_0/k)^{\,j-1}}{(1 + R_0/k)^{\,kj + j - 1}}.$$

For $R_0 \le 1$ these probabilities sum to one (the outbreak is finite almost surely), and for $R_0 < 1$ the mean outbreak size is $\mathbb E[J] = 1/(1-R_0)$; for $R_0 > 1$ the missing mass $1 - \sum_j P(J = j)$ is the probability of an unbounded outbreak.

**Use with importations.** Under independent introductions, the local burden from $m$ imported cases is a sum of $m$ independent copies of $J - 1$, and the number of distinct introductions represented in a random sample of cases depends on how cases are spread across clusters. Matching simulated local-case totals and sampled cluster counts to observations gives likelihood-based estimates of a subcritical $R_0$ under strong heterogeneity (small $k$).

## Depends on

- [Negative-binomial offspring distribution](nb-offspring.md)

## Proof depends on

- [Hitting-time theorem](../../../Probability/branching-processes/total-progeny-and-the-hitting-time-theorem/nat-cast-mul-hitting-weight.md)

## Expansion

By the Lagrange inversion (hitting-time) formula for branching processes, $P(J = j) = \frac1j\,P(X_1 + \dots + X_j = j - 1)$ for i.i.d. offspring counts $X_i$. A sum of $j$ independent negative-binomial$(R_0, k)$ variables is negative binomial with dispersion $kj$ and mean $jR_0$, and evaluating its mass at $j - 1$ and dividing by $j$ gives the displayed formula. The mean follows from $\mathbb E[J] = \sum_{g \ge 0} R_0^g$. Applied to Zika virus in Miami-Dade County in 2016 with $k = 0.1$, local-case counts and the number of genetic clusters among sequenced genomes each gave subcritical estimates, with an overlap of $R_0 \approx 0.5$–$0.8$, implying that local cases came from many separate introductions.

## Sources

- N. D. Grubaugh, J. T. Ladner, M. U. G. Kraemer et al., "Genomic epidemiology reveals multiple introductions of Zika virus into the United States", Nature (2017), Methods (branching-process model of introductions), <https://doi.org/10.1038/nature22400>.
