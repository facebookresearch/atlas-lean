# Conditional square sums of the scaled Nelson–Aalen process converge to the variance function

Let $\mu$ be a measure, $\Lambda$ a continuous cumulative hazard, $\tau > 0$, $t \in [0, \tau]$, and for each $n$ a grid of mesh $\tau/K_n$ ($K_n \to \infty$) carrying $N_n$ and a predictable $Y_n \in \{0\} \cup [1, \infty)$ such that the increments of $M_n = N_n - Y_n\bullet\Lambda$ are $\mu$-square-integrable with the binomial conditional second moment, taken with Mathlib's conditional expectation $\mu[\cdot \mid \mathcal F]$, at the grid steps before $t$. If $y$ is continuous on $[0, \tau]$ with $y \ge \varepsilon > 0$ and $\sup_{\text{grid points}\le t}|Y_n/n - y| \to 0$ in $\mu$-measure, then the conditional square sums of $\sqrt n(\hat A_n - \Lambda^*_n)$ up to $t$ converge in $\mu$-measure (in probability when $\mu$ is a probability measure) to $\int_{(0,t]}y(s)^{-1}d\Lambda(s)$.

## Sources

- P. K. Andersen, Ø. Borgan, R. D. Gill and N. Keiding, "Statistical Models Based on Counting Processes", Springer (1993), §II.5 (Rebolledo's theorem), §IV.1 (the Nelson–Aalen estimator).
