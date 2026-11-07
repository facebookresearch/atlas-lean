# $(p,q)$-analogue of the $r$-Fibonacci polynomial

Let $R$ be a commutative semiring, let
$r$ and $m$ be natural numbers and let $x, y, p, q \in R$. The $(p,q)$-analogue
$U^{(r)}_n(x, y, p, q, m) \in R$ of the $r$-Fibonacci polynomial is defined by
$U^{(r)}_0(x, y, p, q, m) = 0$ and, for every natural number $n$,

$$
U^{(r)}_{n+1}(x, y, p, q, m) = \sum_{k=0}^{\lfloor n/(r+1) \rfloor} p^{\binom{n+1-(r+1)k}{2}}
q^{\binom{k+1}{2} + m \binom{k}{2}} \binom{n-rk}{k}_{p,q} x^{n-(r+1)k} y^k,
$$

where $\binom{a}{b}_{p,q}$ is the $(p,q)$-binomial coefficient.

The source also states $U^{(r)}_j = p^{\binom{j+1}{2}} x^{j-1}$ for $1 \le j \le r$, which
contradicts this sum: the sum gives $p^{\binom{j}{2}} x^{j-1}$ (for example $U^{(2)}_2 = p x$,
not $p^3 x$). The sum, which Theorem 2 of the source requires, is used.

## Sources

- Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025), Article A38, Definition 1.
