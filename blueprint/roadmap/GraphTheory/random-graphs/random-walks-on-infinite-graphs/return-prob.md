# Weighted return sum of a walk

Let $G$ be a simple graph on a vertex set $V$, and let $\deg v$ be the number of neighbours of $v$, taken to be $0$ when $v$ has infinitely many. For a vertex $o$ and a natural number $n$, the $n$-step weighted return sum is the extended nonnegative real

$$p_n(o, o) = \sum_{w} \prod_{i < n} \frac{1}{\deg w_i},$$

the sum over all closed walks $w = (w_0, w_1, \dots, w_n)$ of length $n$ from $o$ to $o$, the product over the vertices the walk leaves, with $1/0 = \infty$. A walk that leaves a vertex with infinitely many neighbours therefore has weight $\infty$: at the centre $o$ of an infinite star, $p_2(o, o) = \infty$. For an isolated vertex $o$, $p_0(o, o) = 1$ and $p_n(o, o) = 0$ for $n \ge 1$. Only when every vertex of $G$ has finitely many neighbours and at least one is $p_n(o, o)$ the probability that simple random walk started at $o$ is at $o$ after $n$ steps.
