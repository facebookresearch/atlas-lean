# Weak-count criterion for the order statistic

Let $\iota$ be a finite set, $f : \iota \to \mathbb{R}$, $k \ge 1$ and $x \in \mathbb{R}$. Then the [$k$-th smallest value](order-statistic.md) satisfies $f_{(k)} \le x$ if and only if at least $k$ values of $f$ are at most $x$:

$$f_{(k)} \le x \iff \#\{i : f(i) \le x\} \ge k.$$

This is the dual of the [strict-count criterion](coe-le-order-statistic-iff.md); it fails for $k = 0$.
