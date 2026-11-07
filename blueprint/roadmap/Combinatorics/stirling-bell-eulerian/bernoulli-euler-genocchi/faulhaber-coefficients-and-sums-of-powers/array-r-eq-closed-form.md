# Closed form for the array $R(k, m)$

Let $k$ and $m$ be natural numbers with
$1 \le m \le k$, and let $R(k, m) = \sum_{j=0}^{m} (-1)^j \binom{2m}{j} (m - j)^{2k}$. Then

$$R(k, m) = 2^{2k+m-1}\, m! \sum_{b} \frac{(2k)!}{b_1! \cdots b_k!}
\prod_{r=1}^{k} \left(\frac{1}{4^r (2r)!}\right)^{b_r},$$

where the sum runs over all $k$-tuples $b = (b_1, \dots, b_k)$ of natural numbers with
$b_1 + 2 b_2 + \dots + k b_k = k$ and $b_1 + \dots + b_k = m$ (each such $b_r$ is at most $k$).

## Sources

- José L. Cereceda, "Sums of Powers of Integers and the Sequence A304330", Corollary 6.
