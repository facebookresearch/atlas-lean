# Primes dividing the coefficient gcd of $(u + v^{1/N})^n$ divide $N$

Let $N \ge 2$ and
let $u, v$ be coprime natural numbers such that $x^N - v$ is irreducible over $\mathbb{Q}$. Write
$\theta = v^{1/N}$ for the nonnegative real $N$-th root of $v$, and let $a_{n,i}$ be integers
($n \ge 1$, $0 \le i < N$) with $(u + \theta)^n = \sum_{i=0}^{N-1} a_{n,i} \theta^i$ for every
$n \ge 1$. If $n \ge 1$ and $p$ is a prime dividing $D_n = \gcd(a_{n,0}, \dots, a_{n,N-1})$,
then $p$ divides $N$.

The paper's section assumes $N \ge 4$; the cases $N = 2, 3$ also hold, while $N = 1$ fails
(there $D_n = (u + v)^n$).

## Sources

- John Ferdinands and Timothy Ferdinands, *Greatest Common Divisors and Lucas's Theorem*, Journal of Integer Sequences 28 (2025), Article 25.2.2, Lemma 8 (`jis-2025-25.2.2-lem-8`).
