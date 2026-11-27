# Existence of a small modulus of large order

For every integer $n \ge 2$ there is an integer $r \le \max\{3, \lceil \log_2 n \rceil^5\}$ such that either $\gcd(r, n) > 1$ or the multiplicative order $\mathrm{ord}_r(n)$ of $n$ modulo $r$ exceeds $(\log_2 n)^2$.

## Proof sketch

Every $r$ with $\gcd(r,n)=1$ and $\mathrm{ord}_r(n) \le (\log_2 n)^2$ divides $\prod_{i \le (\log_2 n)^2}(n^i - 1)$, a number below $2^{(\log_2 n)^5}$. But the least common multiple of $1, \dots, B$ is at least $2^B$ for $B \ge 7$, so not every $r \le B = \lceil \log_2 n \rceil^5$ can divide this product.

## Depends on

- [Multiplicative order modulo $n$](../../../NumberTheory/congruences/congruences-modular-arithmetic/primitive-roots-modulo-prime-powers/mul-ord-mod.md)

## Sources

- M. Agrawal, N. Kayal and N. Saxena, "PRIMES is in P", Annals of Mathematics 160(2), 2004.
