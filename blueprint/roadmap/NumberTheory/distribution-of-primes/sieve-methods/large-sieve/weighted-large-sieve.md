# The Montgomery–Vaughan weighted large sieve

Let $N$ be a natural number, let $a_n$ be complex
numbers, let $\iota$ be a finite index set and for $r \in \iota$ let $x_r$ and $\delta_r > 0$ be
real numbers. Write $\|t\|$ for the distance from a real number $t$ to the nearest integer, and
suppose that $\delta_r \le \|x_r - x_s\|$ for all $r \ne s$. Then

$$
\sum_{r} \left( N + \frac{3}{2 \delta_r} \right)^{-1}
\left| \sum_{n=0}^{N-1} a_n e^{2 \pi i n x_r} \right|^2 \le \sum_{n=0}^{N-1} |a_n|^2.
$$

## Sources

- Montgomery–Vaughan, *The large sieve* (1973), Theorem 1, equations (1.5)–(1.6) and (2.4), lines 227–321. The proof uses duality, the exact geometric sum, and `weightedHilbertCosecant`.
