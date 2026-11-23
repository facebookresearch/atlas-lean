# Splitting a sum by the values on a set of nodes

Let $\alpha$ be a finite type, $P, g : \alpha^n \to \mathbb{R}$, and $S, T$ disjoint finite sets
of nodes such that $g(x)$ depends only on the values of $x$ on $T \cup S$. For every
$x' \in \alpha^n$,

$$\sum_{x \,:\, x_S = x'_S} P(x) \, g(x) = \sum_{t \in \alpha^T} g(x'_t) \, P\big((x'_t)_{T \cup S}\big),$$

where $x'_t$ is [$x'$ overwritten with $t$ on $T$](fill.md) and $P(y_U)$ is the sum of $P(x)$
over the configurations $x$ that agree with $y$ on $U$.
