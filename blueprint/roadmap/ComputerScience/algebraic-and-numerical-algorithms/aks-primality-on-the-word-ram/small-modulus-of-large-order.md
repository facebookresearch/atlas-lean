# Existence of a small modulus of large order

For every integer $n \ge 2$ there is an integer $r \le \max\{3, \lceil (\log_2 n)^5 \rceil\}$ with $\gcd(r, n) = 1$ such that the multiplicative order $\mathrm{ord}_r(n)$ of $n$ modulo $r$ exceeds $(\log_2 n)^2$ (Agrawal, Kayal and Saxena, Lemma 4.3).

## Proof sketch

For $n = 2$ take $r = 3$. For $n > 2$ let $B = \lceil (\log_2 n)^5 \rceil$, so $B > 10$. Every $r \le B$ with $\gcd(r,n)=1$ and $\mathrm{ord}_r(n) \le (\log_2 n)^2$ divides $\prod_{1 \le i \le (\log_2 n)^2}(n^i - 1)$, and every $r \le B$ whose prime factors all divide $n$ divides $n^{\lfloor \log_2 B \rfloor}$; the product $P$ of these two numbers is below $n^{(\log_2 n)^4} \le 2^{(\log_2 n)^5} \le 2^B$. The least common multiple of $1, \dots, B$ is at least $2^B$ for $B \ge 7$, so some $s \le B$ does not divide $P$. Its largest divisor $r$ coprime to $n$ then does not divide $\prod_i (n^i - 1)$, since the rest of $s$ divides $n^{\lfloor \log_2 B \rfloor}$; hence $\gcd(r, n) = 1$, $r \le B$ and $\mathrm{ord}_r(n) > (\log_2 n)^2$.

## Depends on

- [Multiplicative order modulo $n$](../../../NumberTheory/congruences/congruences-modular-arithmetic/primitive-roots-modulo-prime-powers/mul-ord-mod.md)

## Sources

- M. Agrawal, N. Kayal and N. Saxena, "PRIMES is in P", Annals of Mathematics 160(2), 2004.
