# Multiclass weak learnability relative to random guessing on lists

Let $H \subseteq Y^X$ and $\gamma > 0$. A hypothesis $h : X \to Y$ satisfies the **$\gamma$-BRG condition** (better than random guess) with respect to a list function $\mu : X \to Y^k$ and a distribution $D$ over $X \times Y$ if

$$
\Pr_{(x,y) \sim D}[h(x) = y] \ge \Big(\frac{1}{k} + \gamma\Big) \Pr_{(x,y) \sim D}[y \in \mu(x)].
$$

A learning rule $W$, which receives examples and a list function, satisfies the $\gamma$-BRG condition for $H$ if for every $H$-realizable $D$, every $k \ge 2$ and every list function $\mu : X \to Y^k$, given $m_0(\delta)$ i.i.d. examples from $D$ and $\mu$, it outputs with probability at least $1 - \delta$ a hypothesis satisfying this inequality. The **empirical** $\gamma$-BRG condition for a sample $S = ((x_i, y_i))_{i \le m}$ asks the same for every distribution $p$ over $[m]$, every $k \ge 2$ and every list function on the points of $S$, with $m_0$ examples drawn from $S$ according to $p$:

$$
\sum_{i=1}^m p_i\, \mathbf{1}[h(x_i) = y_i] \ge \Big(\frac{1}{k} + \gamma\Big) \sum_{i=1}^m p_i\, \mathbf{1}[y_i \in \mu(x_i)].
$$

The condition says that whenever the label lies in the list, $h$ beats a uniform guess from the list by the margin $\gamma$. For $Y = \{0,1\}$ and the list of both labels it is the classical weak learning condition $\Pr[h(x) = y] \ge \tfrac12 + \gamma$.

## Depends on

- [The realizable distribution family](../../../occam-bound-for-consistent-learners/realizable-family.md)

## Sources

- N. Brukhim, A. Daniely, Y. Mansour, S. Moran, "Multiclass Boosting: Simple and Intuitive Weak Learning Criteria", NeurIPS (2023), arXiv:2307.00642, Definitions 1 and 2.
