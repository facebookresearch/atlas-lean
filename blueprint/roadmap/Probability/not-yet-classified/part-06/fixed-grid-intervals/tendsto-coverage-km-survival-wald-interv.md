# Kaplan-Meier Wald interval at a grid time

Let $W_1, W_2, \dots$ be i.i.d. observations of $((T, J), C)$ on a finite time grid, where the event time and cause $(T, J)$ have law $p_{TJ}$ and are independent of the censoring time $C$ with law $p_C$. Fix a grid index $m$ with $P(\min(T, C) \ge m) \ne 0$ and $j \le m$, and suppose the asymptotic variance $\sigma^2$ of the Kaplan-Meier estimator at $j$ is positive. Let $\mathrm{se}_n$ be almost everywhere measurable with $\mathrm{se}_n \to \sigma$ in probability. Then, with $\hat S_n(j)$ the Kaplan-Meier estimate from the first $n$ observations,

$$P\Big(P(T > j) \in \big[\hat S_n(j) - z\,\mathrm{se}_n/\sqrt n,\ \hat S_n(j) + z\,\mathrm{se}_n/\sqrt n\big]\Big) \to P(-z \le Z \le z), \qquad Z \sim N(0,1).$$
