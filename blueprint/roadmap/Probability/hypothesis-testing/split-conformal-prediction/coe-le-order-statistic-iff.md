# Strict-count criterion for the order statistic

Let $\iota$ be a finite set, $f : \iota \to \mathbb{R}$, $k \ge 1$ and $x \in \mathbb{R}$. Then $x \le f_{(k)}$, the [$k$-th smallest value](order-statistic.md) of $f$, if and only if fewer than $k$ values of $f$ are strictly below $x$:

$$x \le f_{(k)} \iff \#\{i : f(i) < x\} < k.$$
