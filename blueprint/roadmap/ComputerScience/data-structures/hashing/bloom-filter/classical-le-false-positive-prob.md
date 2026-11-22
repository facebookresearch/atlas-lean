# Bloom's formula is a lower bound

Let $m, n, k \in \mathbb{N}$ with $m > 0$. The exact false-positive rate under uniform hashing,
for $m$ bits, $n$ stored elements and $k$ hash functions, is at least Bloom's formula

$$\left(1 - \left(1 - \frac{1}{m}\right)^{n k}\right)^{k}.$$

This follows from Jensen's inequality for $t \mapsto t^k$.
