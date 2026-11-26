# Criterion for lying below the weighted quantile

Let $\iota$ be a finite index set, $\beta > 0$, $v : \iota \to \mathbb{R}$ and $p : \iota \to \mathbb{R}$ with $p_i \ge 0$ for all $i$. For every real $x$, $x \le Q_\beta(v, p)$ (the [weighted quantile](weighted-quantile.md)) if and only if the total weight of the scores strictly below $x$ is less than $\beta$:

$$x \le Q_\beta(v, p) \iff \sum_{i :\ v_i < x} p_i < \beta.$$
