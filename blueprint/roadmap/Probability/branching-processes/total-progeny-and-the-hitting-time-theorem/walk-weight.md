# Walk weight of step sequences ending at zero

For a function $p : \mathbb{N} \to R$ with values in a commutative semiring $R$ and for
$k, n \in \mathbb{N}$, the walk weight is

$$W_p(k, n) = \sum_{x} \prod_{i < n} p(x_i) ,$$

the sum over the $x \in \mathbb{N}^n$ with $x_0 + \dots + x_{n-1} + k = n$: the walk started at
$k$ with steps $x_i - 1$ is at $0$ at time $n$. It is $0$ when $k > n$. For
$p(j) = P(\xi = j)$ and $k \le n$ this is $P(\xi_1 + \dots + \xi_n = n - k)$ for i.i.d. $\xi_i$.
