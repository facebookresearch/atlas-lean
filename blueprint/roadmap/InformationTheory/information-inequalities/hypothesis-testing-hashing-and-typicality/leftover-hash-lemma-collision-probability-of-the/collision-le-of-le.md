# Collision probability is at most the maximum mass

Let $p$ be a probability mass function on a finite set $X$, so $p(x) \ge 0$ and $\sum_x p(x) = 1$. If $p(x) \le M$ for all $x$, then the collision probability satisfies $\sum_x p(x)^2 \le M$.

In particular, for nonempty $X$, taking $M = \max_x p(x)$ gives $\sum_x p(x)^2 \le \max_x p(x)$; conversely, that bound implies the bound for every $M \ge \max_x p(x)$.
