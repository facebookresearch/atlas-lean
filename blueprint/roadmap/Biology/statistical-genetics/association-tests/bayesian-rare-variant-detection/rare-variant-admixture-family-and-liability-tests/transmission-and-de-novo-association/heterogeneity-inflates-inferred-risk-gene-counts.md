# Heterogeneity inflates the number of risk genes inferred from recurrent mutations

Let a disorder have $K$ risk genes among those sequenced, let gene $k$ have per-generation, per-chromosome de novo mutation probability $m_k$ and let $N$ trios be sequenced. If a risk gene is hit by de novo events at rate $\lambda_k = 2 N m_k \gamma_k$ with $\gamma_k$ its relative risk, and the events in each gene form an independent Poisson count, the number $R$ of **multiple-hit** genes, risk genes carrying at least two independent de novo events, has expectation

$$\mathbb{E} R = \sum_{k=1}^{K} \Pr(\mathrm{Poisson}(\lambda_k) \ge 2) = \sum_{k=1}^{K} g(\lambda_k), \qquad g(\lambda) = 1 - e^{-\lambda}(1 + \lambda).$$

**Convexity in the rare-event range.** $g'(\lambda) = \lambda e^{-\lambda}$ and $g''(\lambda) = (1 - \lambda) e^{-\lambda}$, so $g$ is convex on $[0, 1]$ and concave on $[1, \infty)$. If every rate satisfies $0 \le \lambda_k \le 1$, then by Jensen's inequality, with $\bar{\lambda} = K^{-1}\sum_k \lambda_k$,

$$\mathbb{E} R \;=\; K \cdot \frac{1}{K}\sum_k g(\lambda_k) \;\ge\; K \, g(\bar{\lambda}).$$

The restriction matters: with $K = 2$ and rates $2$ and $4$, $\mathbb{E} R \approx 1.5024$, less than $2 g(3) \approx 1.6017$. For rare events the inequality is the statement that spreading a fixed total rate unevenly over the risk genes raises the expected number of genes hit twice or more.

**The inference it supports.** He et al. fit the number of risk genes $K$ and the distribution of relative risks jointly, using the observed total number of de novo events and a model for how risk varies across genes, rather than by inverting the inequality above. Under that model, an analysis that assumes all risk genes equally mutable and equally risky explains the observed recurrences with fewer risk genes than one that allows the spread, and for autism the estimate rose from a few hundred risk genes to roughly a thousand, with average relative risk about twenty, on the same de novo data. At a fixed total de novo excess the model trades $K$ against the average relative risk $\bar\gamma$, and only the pattern of recurrence, not the total count, separates the two.

## Depends on

- [Poisson counts of de novo and transmitted variants in trios](poisson-counts-of-de-novo-and-transmitted-variants.md)

## Proof depends on

- [Jensen's inequality](../../../../../../MeasureTheory/integration/jensen-s-inequality-for-integrals/jensen-s-inequality/jensen-inequality.md)

## Expansion

The identity for $\mathbb{E} R$ is linearity of expectation over the indicators of the events $\{\mathrm{Poisson}(\lambda_k) \ge 2\}$. The inequality is Jensen's inequality for the uniform distribution on the $K$ rates, applied to a convex function on the real line that agrees with $g$ on $[0, 1]$ (for instance $g$ on $[0, 1]$ continued by its tangent lines at the endpoints). Within that range its direction is fixed by convexity alone, so it holds whatever the source of the heterogeneity: gene length and sequence context acting through $m_k$, or variation in penetrance acting through $\gamma_k$. Outside it the comparison can go either way, which is why the cited analysis rests on a fitted model of the risk distribution and not on the inequality, and why the number of multiple-hit genes is pooled with inherited and case–control information, each carrying its own dependence on $(K, \bar\gamma)$, to separate the two parameters.

## Sources

- X. He, S. J. Sanders, L. Liu et al., "Integrated model of de novo and inherited genetic variants yields greater power to identify risk genes", PLoS Genetics 9 (2013), e1003671, Results ("Genetic architecture of ASD", Fig. 3A,B) and Text S1 (Eq. 27 and the Jensen's-inequality argument), <https://doi.org/10.1371/journal.pgen.1003671>, PMCID PMC3744441.
