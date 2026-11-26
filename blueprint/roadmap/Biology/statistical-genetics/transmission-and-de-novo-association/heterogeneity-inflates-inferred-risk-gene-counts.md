# Heterogeneity inflates the number of risk genes inferred from recurrent mutations

Let a disorder have $K$ risk genes among those sequenced, let gene $k$ have per-trio de novo mutation probability $m_k$ and let $N$ trios be sequenced. If a risk gene is hit by de novo events at rate $\lambda_k = 2 N m_k \gamma_k$ with $\gamma_k$ its relative risk, the number of **multiple-hit** genes — risk genes carrying at least two independent de novo events — has expectation

$$\mathbb{E} R = \sum_{k=1}^{K} \Pr(\mathrm{Poisson}(\lambda_k) \ge 2) = \sum_{k=1}^{K} g(\lambda_k), \qquad g(\lambda) = 1 - e^{-\lambda}(1 + \lambda).$$

**Convexity and the bias.** $g$ is convex on $[0, \infty)$, since $g''(\lambda) = \lambda e^{-\lambda} \ge 0$. Hence by Jensen's inequality, with $\bar{\lambda} = K^{-1}\sum_k \lambda_k$,

$$\mathbb{E} R \;=\; K \cdot \frac{1}{K}\sum_k g(\lambda_k) \;\ge\; K \, g(\bar{\lambda}).$$

An estimator that equates the observed number of multiple-hit genes to $K g(\bar\lambda)$, that is one that assumes all risk genes equally mutable and equally risky, therefore solves for a $K$ no larger than the truth: heterogeneity in mutation rate or in relative risk across risk genes concentrates recurrences in a few genes, so the same number of recurrences is produced by more risk genes than the homogeneous calculation reports. Allowing the spread, the estimate for autism rose from a few hundred risk genes to roughly a thousand, with average relative risk about twenty, on the same de novo data.

**Inverse relation between count and effect.** At fixed observed numbers of de novo events, $K$ and the average relative risk $\bar\gamma$ trade off: the total de novo excess over the null pins down the product, so halving the assumed risk roughly doubles the inferred number of risk genes. Only the pattern of recurrence, not the total count, separates the two.

## Depends on

- [Poisson counts of de novo and transmitted variants in trios](poisson-counts-of-de-novo-and-transmitted-variants.md)

## Expansion

The inequality is Jensen applied to $g$ at the empirical distribution of $\lambda_k$ over risk genes, and its direction is fixed by convexity alone, so it holds whatever the source of the heterogeneity — gene length and sequence context acting through $m_k$, or variation in penetrance acting through $\gamma_k$. The gap is not small: with a mutation-rate distribution as skewed as the observed one, the right-hand side underestimates the left by a factor of order two in realistic regimes, which is the whole discrepancy between the two published estimates of the number of autism risk genes. The same convexity argument is why the number of multiple-hit genes is a weak statistic for $K$ in isolation and why pooling it with inherited and case–control information, each carrying its own dependence on $(K, \bar\gamma)$, is needed to separate the two parameters.

## Sources

- X. He, S. J. Sanders, L. Liu et al., "Integrated model of de novo and inherited genetic variants yields greater power to identify risk genes", PLoS Genetics 9 (2013), e1003671, Results ("Genetic architecture of ASD", Fig. 3A,B) and Text S1 (Eq. 27 and the Jensen's-inequality argument), <https://doi.org/10.1371/journal.pgen.1003671>, PMCID PMC3744441.
