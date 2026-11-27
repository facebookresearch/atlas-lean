# Conditional square sums of the scaled Nelson–Aalen process converge to the variance function

Let $\mu$ be a measure, $\Lambda$ a continuous cumulative hazard, $\tau > 0$, $t \in [0, \tau]$, and for each $n$ a grid of mesh $h_n = \tau/K_n$ ($K_n \to \infty$) carrying $N_n$ and a predictable $Y_n \in \{0\} \cup [1, \infty)$ such that the increments of $M_n = N_n - Y_n\bullet\Lambda$ are $\mu$-square-integrable with the binomial conditional second moment, taken with Mathlib's conditional expectation $\mu[\cdot \mid \mathcal F]$, at the steps $j < \lfloor t/h_n\rfloor_+$ (the natural-number floor). If $y$ is continuous on $[0, \tau]$ with $y \ge \varepsilon > 0$ and, for every $\delta > 0$, $\mu(\exists i < \lfloor t/h_n\rfloor_+ : |Y_n(i+1)/n - y((i+1)h_n)| > \delta) \to 0$ (the comparison is at the positive right endpoints $(i+1)h_n \le t$; the initial value $Y_n(0)$ is not involved), then the conditional square sums of $\sqrt n(\hat A_n - \Lambda^*_n)$ up to step $\lfloor t/h_n\rfloor_+$ converge in $\mu$-measure (in probability when $\mu$ is a probability measure) to $\int_{(0,t]}y(s)^{-1}d\Lambda(s)$.

## Sources

- P. K. Andersen, Ø. Borgan, R. D. Gill and N. Keiding, "Statistical Models Based on Counting Processes", Springer (1993), §II.5 (Rebolledo's theorem), §IV.1 (the Nelson–Aalen estimator).
