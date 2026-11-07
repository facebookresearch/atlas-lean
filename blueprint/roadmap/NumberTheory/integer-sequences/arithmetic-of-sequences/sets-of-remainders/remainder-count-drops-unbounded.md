# Unbounded drops in the number of remainders

Let $s(n)$ be the number of distinct
remainders $n \bmod k$ with $1 \le k \le \lfloor n/2 \rfloor$. For every natural number $M$
there are infinitely many $n$ with $s(n+1) + M \le s(n)$; equivalently,
$\liminf_{n \to \infty} (s(n+1) - s(n)) = -\infty$.

## Sources

- Omkar Baraskar and Ingrid Vukusic, *Bounds for Sets of Remainders*, Journal of Integer Sequences 29 (2026), Article 26.1.4, Proposition 17 (`prop:diffs_unbounded`).
