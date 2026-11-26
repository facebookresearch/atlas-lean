# Blockwise lasso reduction and the graphical lasso algorithm

In the setting of the [graphical lasso](graphical-lasso-objective-and-optimality.md), permute so the target variable is last and partition

$$W = \begin{pmatrix} W_{11} & w_{12} \\ w_{12}^\top & w_{22} \end{pmatrix}, \quad S = \begin{pmatrix} S_{11} & s_{12} \\ s_{12}^\top & s_{22} \end{pmatrix}, \quad \Theta = \begin{pmatrix} \Theta_{11} & \theta_{12} \\ \theta_{12}^\top & \theta_{22} \end{pmatrix}.$$

**Reduction.** With $W_{11}$ fixed and positive definite, the upper-right block $w_{12} - s_{12} - \rho\gamma_{12} = 0$ of the optimality condition is equivalent to $w_{12} = W_{11}\beta$, where $\beta$ solves the lasso problem

$$\min_{\beta \in \mathbb R^{p-1}}\ \tfrac12 \bigl\lVert W_{11}^{1/2}\beta - W_{11}^{-1/2} s_{12}\bigr\rVert^2 + \rho \lVert\beta\rVert_1,$$

and then $\theta_{12} = -\theta_{22}\beta$ with $\theta_{22} = 1/(w_{22} - w_{12}^\top\beta)$.

**Algorithm.** Start with $W = S + \rho I$ (the diagonal is never changed). Cycle over $j = 1, \dots, p, 1, \dots$: solve the lasso above with inputs $W_{11}$, $s_{12}$ by coordinate descent,

$$\hat\beta_j \leftarrow \frac{\mathcal S\bigl(u_j - \sum_{k \ne j} V_{kj}\hat\beta_k,\ \rho\bigr)}{V_{jj}}, \qquad V = W_{11},\ u = s_{12},\ \mathcal S(x, t) = \operatorname{sign}(x)(|x| - t)_+,$$

then set $w_{12} = W_{11}\hat\beta$; stop when $W$ stabilizes, and recover $\hat\Theta$ column by column from the stored $\beta$'s. If $W_{11}$ is replaced by $S_{11}$, the inner problem is the lasso regression of variable $p$ on the others (the Meinshausen–Bühlmann approximation); with $\rho = 0$, if moreover $S \succ 0$ (which fails, for example, for a centred sample with $p \ge N$, whose rank is at most $N - 1$), then $W = S$ and one sweep computes $S^{-1}$ by partitioned inversion. The case $\rho > 0$ needs no such assumption: $W = S + \rho I$ is positive definite for every $S \succeq 0$.

## Expansion

The subgradient equation of the lasso problem is $W_{11}\beta - s_{12} + \rho\nu = 0$ with $\nu \in \operatorname{sign}(\beta)$. From $W\Theta = I$ the upper-right block gives $W_{11}\theta_{12} + w_{12}\theta_{22} = 0$, so $\theta_{12} = -\theta_{22} W_{11}^{-1} w_{12}$; since $\theta_{22} > 0$, $\operatorname{sign}(\theta_{12}) = -\operatorname{sign}(W_{11}^{-1} w_{12})$. Hence $(w_{12}, \gamma_{12})$ solves the block equation iff $\beta = W_{11}^{-1} w_{12}$ and $\nu = -\gamma_{12}$ solve the lasso subgradient equation. The bottom-right block of $W\Theta = I$ gives $\theta_{22}$.

## Depends on

- [Graphical lasso objective and optimality conditions](graphical-lasso-objective-and-optimality.md)

## Sources

- J. Friedman, T. Hastie and R. Tibshirani, "Sparse inverse covariance estimation with the graphical lasso", *Biostatistics* 9 (2008), 432–441, <https://doi.org/10.1093/biostatistics/kxm045> (PMC3019769). Equations (2.2)–(2.14) and the graphical lasso algorithm in Section 2.
