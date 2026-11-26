# The density of an exponential family sums to one

Let $X$ be a finite set, $\iota$ a finite index set, $h : X \to \mathbb{R}$ base weights with $h(x) \ge 0$ for every $x$ and $\sum_{x} h(x) > 0$, and $T : X \to \mathbb{R}^\iota$ a sufficient statistic. Write $A(\eta) = \log \sum_{x} h(x) e^{\eta \cdot T(x)}$ for the log-partition function, $p_\eta(x) = h(x) e^{\eta \cdot T(x) - A(\eta)}$ for the density and $\mu(\eta) = \sum_x p_\eta(x) T(x)$ for the mean of the statistic, at $\eta \in \mathbb{R}^\iota$. Then for every $\eta$,

$$\sum_{x \in X} p_\eta(x) = 1.$$
