# Product formula from the mesh-pattern recurrence

Let $R$ be a commutative semiring, let
$x \in R$, let $0 < k \le n$ be natural numbers, and let $P(m, r) \in R$ for natural numbers
$m, r$. Natural numbers are mapped into $R$. Suppose that $P(k-1, k) = (k-1)!$ and that
$P(m, k) = (x + (m - 1))\,P(m-1, k)$ for every natural number $m \ge k$. Then

$$P(n, k) = (k-1)! \prod_{i=0}^{n-k} \bigl(x + (k - 1 + i)\bigr).$$

With $R$ the polynomials over $\mathbb{N}$ and $x$ the variable, this is the product formula for
the mesh-pattern counting polynomial.

## Sources

- Matt Davis, "Quadrant Marked Mesh Patterns and the r-Stirling Numbers," Journal of Integer Sequences 18 (2015), Article 15.10.1, Corollary, line 194, with the recurrence and base value from Theorem, line 175, <https://cs.uwaterloo.ca/journals/JIS/VOL18/Davis/davis3.tex>.
