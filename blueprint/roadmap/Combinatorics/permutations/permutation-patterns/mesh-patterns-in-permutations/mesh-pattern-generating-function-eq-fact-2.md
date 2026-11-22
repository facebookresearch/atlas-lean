# Product formula from the mesh-pattern recurrence, real case

Let $0 < k \le n$ be natural
numbers, let $x$ be a real number, and let $P(m, r, y)$ be real numbers indexed by natural
numbers $m, r$ and a real number $y$. Suppose that $P(k-1, k, x) = (k-1)!$ and that
$P(m, k, x) = (x + m - 1)\,P(m-1, k, x)$ for every natural number $m \ge k$. Then

$$P(n, k, x) = (k-1)! \prod_{i=0}^{n-k} (x + k - 1 + i).$$

## Sources

- Matt Davis, "Quadrant Marked Mesh Patterns and the r-Stirling Numbers," Journal of Integer Sequences 18 (2015), Article 15.10.1, Corollary 4, with the recurrence and base value of Theorem 3, <https://cs.uwaterloo.ca/journals/JIS/VOL18/Davis/davis3.pdf>.
