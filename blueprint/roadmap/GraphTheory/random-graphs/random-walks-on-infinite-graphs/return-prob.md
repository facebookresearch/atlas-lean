# Weighted return sum of a walk

Let $G$ be a simple graph on a vertex set $V$, and let $\deg v$ be the number of neighbours of $v$, taken to be $0$ when $v$ has infinitely many. For a vertex $o$ and a natural number $n$, the $n$-step weighted return sum is the extended nonnegative real

$$p_n(o, o) = \sum_{w} \prod_{i < n} \frac{1}{\deg w_i},$$

the sum over all closed walks $w = (w_0, w_1, \dots, w_n)$ of length $n$ from $o$ to $o$, the product over the vertices the walk leaves, with $1/0 = \infty$. A walk that leaves a vertex with infinitely many neighbours therefore has weight $\infty$: at the centre $o$ of an infinite star, $p_2(o, o) = \infty$. For an isolated vertex $o$, $p_0(o, o) = 1$ and $p_n(o, o) = 0$ for $n \ge 1$. If every vertex in the connected component of $o$ has finitely many neighbours and at least one, then $p_n(o, o)$ is the probability that simple random walk started at $o$ is at $o$ after $n$ steps. Vertices outside that component do not matter: in the disjoint union of $K_2$ and an infinite star, the walk from a vertex of $K_2$ alternates deterministically, and its weighted return sums are its return probabilities.
