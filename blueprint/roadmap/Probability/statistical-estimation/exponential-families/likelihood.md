# Likelihood of observations in an exponential family

Let $X$ be a finite set, $\iota$ a finite index set, $h : X \to \mathbb{R}$ base weights and $T : X \to \mathbb{R}^\iota$ a sufficient statistic, with density $p_\eta(x) = h(x) e^{\eta \cdot T(x) - A(\eta)}$, where $A(\eta) = \log \sum_x h(x) e^{\eta \cdot T(x)}$. The likelihood of observations $x_1, \dots, x_m \in X$ at $\eta \in \mathbb{R}^\iota$ is

$$L(\eta) = \prod_{k=1}^m p_\eta(x_k).$$

It is the likelihood of an exponential family when $h \ge 0$ and $\sum_x h(x) > 0$.
