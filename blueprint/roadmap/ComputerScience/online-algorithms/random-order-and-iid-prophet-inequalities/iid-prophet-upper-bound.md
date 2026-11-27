# No stopping rule beats $\beta$ for i.i.d. values

For every $\varepsilon > 0$ there is $n$ and an i.i.d. instance of nonnegative $X_1, \dots, X_n$ with $0 < \mathbb{E}[\max_i X_i] < \infty$ such that every stopping rule $\tau$ satisfies $\mathbb{E}[X_\tau] \le (\beta + \varepsilon)\,\mathbb{E}[\max_i X_i]$, where $\beta \approx 0.745$ is the Hill–Kertz constant.

## Proof sketch

Hill and Kertz reduce the worst case to distributions for which the optimal dynamic-programming stopping values form a specific recursion; Kertz solves the limiting recursion by conjugate duality, showing that the worst-case ratio converges to the root $\beta$ of the defining integral equation, and the extremal distributions realize it in the limit.

## Depends on

- [The Hill–Kertz constant $\beta \approx 0.745$](hill-kertz-constant.md)
- [Gambler-to-prophet ratios under different arrival models](prophet-ratio-by-arrival-model.md)

## Sources

- Theodore P. Hill, Robert P. Kertz, "Comparisons of Stop Rule and Supremum Expectations of I.I.D. Random Variables", Annals of Probability 10(2) (1982).
- Robert P. Kertz, "Stop Rule and Supremum Expectations of I.I.D. Random Variables: A Complete Comparison by Conjugate Duality", Journal of Multivariate Analysis 19(1) (1986).
