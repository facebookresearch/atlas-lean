# Generating function for words with alternating repeated letters

The following holds. For every $k \in \mathbb{N}$, as formal power series over $\mathbb{Q}$,

$$\sum_{n \ge 0} f_k(n) x^n = -\frac{(k-2)x^3 + 2(k-2)x^2 + (k-3)x - 1}{2(k-1)^2 x^3 + (k-1)(k-4)x^2 + (3-2k)x + 1},$$

where division means multiplication by the inverse of the denominator in $\mathbb{Q}[[x]]$ (its constant term is $1$). The constant term $1$ on the right is $f_k(0)$, the count of the empty word, so the identity holds from $n = 0$.

For $k, n \in \mathbb{N}$, $f_k(n)$ is the number of words $w = w_0 w_1 \cdots w_{n-1}$ of length $n$ over a $k$-letter alphabet with the following property: whenever $0 \le i < j$ with $j + 1 < n$, $w_i = w_{i+1}$ and $w_j = w_{j+1} = w_i$, there is $m$ with $i < m < j$ such that $w_m = w_{m+1} \neq w_i$.

## Sources

- Sela Fried, "Proofs of Several Conjectures From the OEIS", Journal of Integer Sequences 28 (2025), Article 25.4.3, Theorem 4.
