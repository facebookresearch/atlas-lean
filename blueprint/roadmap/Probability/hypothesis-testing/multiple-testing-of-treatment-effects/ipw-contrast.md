# Inverse-probability-weighted contrast

For a treatment event $T$, a covariate $X$ with propensity score $e(x) = P(T \mid X = x)$ and an observed outcome $Y$, the inverse-probability-weighted contrast is $\mathbb{E}\big[\mathbf 1_TY/e(X) - \mathbf 1_{T^c}Y/(1 - e(X))\big]$; it depends only on the law of $(T, X, Y)$. Quotients with $e(X) = 0$ or $1 - e(X) = 0$ are read as $0$.

## Sources

- the left-hand side of `integral_ipw_ate` (Horvitz & Thompson 1952; Rosenbaum 1987).
