# Validity of a discrete upper-tail p-value

Let $s$ be a finite set, $q, T : s \to \mathbb{R}$ with $q \ge 0$, and $t \ge 0$. With the upper-tail weight $p(x) = \sum_{y \in s,\ T(x) \le T(y)} q(y)$,

$$\sum_{x \in s,\ p(x) \le t} q(x) \le t.$$

When $q$ is a probability mass function on $s$ and $T$ a test statistic, $p(x)$ is the upper-tail p-value of $x$, and the inequality says that the test rejecting when $p \le t$ has level $t$.
