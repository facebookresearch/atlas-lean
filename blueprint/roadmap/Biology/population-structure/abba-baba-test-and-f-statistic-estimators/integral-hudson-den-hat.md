# Hudson's denominator is unbiased

Let $\mu$ be a measure, let $m_A, m_B \ge 1$ and $q_A, q_B \in [0, 1]$, and let $X_A, X_B$ be independent under $\mu$ with binomial laws $\mathrm{Bin}(m_A, q_A)$ and $\mathrm{Bin}(m_B, q_B)$. Then the [denominator estimator](hudson-den-hat.md) satisfies (Bhatia et al. 2013)

$$\int \hat D(m_A, m_B, X_A, X_B) \, d\mu = D(q_A, q_B),$$

where $D$ is [Hudson's denominator](hudson-den.md).

## Sources

- G. Bhatia, N. Patterson, S. Sankararaman, A. L. Price, *Estimating and interpreting $F_{ST}$: the impact of rare variants*, Genome Res. 23 (2013), 1514–1521.
