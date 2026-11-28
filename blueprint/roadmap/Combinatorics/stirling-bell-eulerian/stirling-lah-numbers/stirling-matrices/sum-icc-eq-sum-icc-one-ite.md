# Writing a sum over k, …, n as a sum over 1, …, n

Let $M$ be an additive commutative monoid, let $f \colon \mathbb{N} \to M$, and let $k$ and $n$ be natural numbers with $1 \le k$. Then

$$\sum_{l=k}^{n} f(l) = \sum_{l=1}^{n} \begin{cases} f(l) & \text{if } k \le l, \\ 0 & \text{otherwise.} \end{cases}$$
