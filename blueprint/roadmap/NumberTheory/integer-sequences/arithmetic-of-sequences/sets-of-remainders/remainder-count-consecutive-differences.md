# Consecutive differences of the number of remainders

Let $s(n)$ be the number of
distinct remainders $n \bmod k$ with $1 \le k \le \lfloor n/2 \rfloor$. Then
$s(n+1) \le s(n) + 1$ for every $n \ge 1$; there is a real constant $C$ with
$s(n) - C \log \log n \le s(n+1)$ for all sufficiently large $n$; and for every natural number
$M$ there are infinitely many $n$ with $s(n+1) + M \le s(n)$, that is,
$\liminf_{n \to \infty} (s(n+1) - s(n)) = -\infty$.

## Sources

- Omkar Baraskar and Ingrid Vukusic, *Bounds for Sets of Remainders*, Journal of Integer Sequences 29 (2026), Article 26.1.4, Theorem 2 (`thm:diffs`).
