# Weighted quantile with an atom at $+\infty$

Let $\iota$ be a finite index set, $\beta \in \mathbb{R}$ a level, $v : \iota \to \mathbb{R}$ scores and $p : \iota \to \mathbb{R}$ weights. The weighted quantile is the least score $v_j$ whose cumulative weight is at least $\beta$,

$$Q_\beta(v, p) = \min\Big\{v_j : \sum_{i :\ v_i \le v_j} p_i \ge \beta\Big\},$$

and $+\infty$ if there is none. When the $p_i$ are nonnegative with $\sum_i p_i \le 1$, so that the remaining mass $p_\infty = 1 - \sum_i p_i \ge 0$ sits at $+\infty$, and $0 < \beta \le 1$, this is the level-$\beta$ quantile $\inf\{t : F(t) \ge \beta\}$ of $F = \sum_i p_i \delta_{v_i} + p_\infty \delta_{+\infty}$, the quantity $\mathrm{Quantile}(\beta; \sum_i p_i \delta_{v_i} + p_{n+1} \delta_\infty)$ of Tibshirani, Barber, Candès and Ramdas (NeurIPS 2019, arXiv:1904.06019, Corollary 1).
