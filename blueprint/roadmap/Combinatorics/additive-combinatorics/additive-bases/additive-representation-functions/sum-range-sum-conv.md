# Total of a sum convolution of finitely supported sequences

Let $R$ be a semiring, not necessarily commutative, and let $f, g \colon \mathbb{N} \to R$. Write the sum convolution $(f * g)(n) = \sum_{a + b = n} f(a)\, g(b)$, the sum over all pairs $(a, b)$ of natural numbers with $a + b = n$. Let $n, m \in \mathbb{N}$ be such that $f(i) = 0$ for every $i \ge n$ and $g(j) = 0$ for every $j \ge m$. Then

$$\sum_{k=0}^{n+m-1} (f * g)(k) = \Big( \sum_{i=0}^{n-1} f(i) \Big) \Big( \sum_{j=0}^{m-1} g(j) \Big),$$

with the two totals multiplied in this order. Empty sums are $0$, so the identity reads $0 = 0$ when $n = 0$ or $m = 0$.
