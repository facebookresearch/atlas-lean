# MR-Egger line is the weighted least-squares line

Let $\iota$ be a finite set of SNPs, let $v_j \ge 0$ for every $j$, and let $\hat\beta_X, \hat\beta_Y \in \mathbb{R}^\iota$ with $\operatorname{Var}_v(\hat\beta_X) \ne 0$. Then for all $a, b \in \mathbb{R}$,

$$S_E(a_E, b_E) \le S_E(a, b),$$

where $S_E$ is the [weighted residual sum of squares](egger-ssr.md), and $a_E, b_E$ are the [MR-Egger intercept](egger-intercept.md) and [slope](egger-slope.md).
