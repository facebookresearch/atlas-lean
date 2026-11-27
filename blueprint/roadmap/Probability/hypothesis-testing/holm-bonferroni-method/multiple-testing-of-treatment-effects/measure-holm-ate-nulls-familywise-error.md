# Holm over causal nulls

Let $T$ be a measurable treatment event on a probability space, $X$ a measurable covariate with finitely many values, $e(x) = P(T \mid X = x)$ the propensity score, and for endpoints $j = 1, \dots, m$ potential outcomes $Y_{0j}, Y_{1j}$ with observed outcome $Y_j = Y_{1j}$ on $T$ and $Y_{0j}$ off $T$. The causal nulls are the endpoints with integrable $Y_{1j} - Y_{0j}$ and $\mathbb{E}[Y_{1j} - Y_{0j}] = 0$; p-values are calibrated if $p_j$ is valid whenever the inverse-probability-weighted contrast $\mathbb{E}[\mathbf 1_TY_j/e(X) - \mathbf 1_{T^c}Y_j/(1 - e(X))]$ of $Y_j$ is integrable and zero. Suppose every causal-null endpoint has measurable, integrable potential outcomes and is strongly ignorable given $X$ (positivity and exchangeability), and the p-values are calibrated. Then for $\alpha \in [0, 1]$, Holm's step-down procedure rejects some causal-null endpoint with probability at most $\alpha$, with no assumption on the dependence of the p-values.

## Sources

- Holm (1979); identification as in Rosenbaum & Rubin (1983).
