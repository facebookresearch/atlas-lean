# Return probability of simple random walk

Let $G$ be a simple graph on a vertex set $V$. For a vertex $o$ and a natural number $n$, the $n$-step return probability is the extended nonnegative real

$$p_n(o, o) = \sum_{w} \prod_{i < n} \frac{1}{\deg w_i},$$

the sum over all closed walks $w = (w_0, w_1, \dots, w_n)$ of length $n$ from $o$ to $o$, the product over the vertices the walk leaves ($1/0 = \infty$).
