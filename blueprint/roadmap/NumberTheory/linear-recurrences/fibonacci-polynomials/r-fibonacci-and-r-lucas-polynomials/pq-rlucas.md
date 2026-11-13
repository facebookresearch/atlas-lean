# First-kind (p, q)-Lucas polynomials

Let $R$ be a commutative semiring, let $r$, $s$ and
$m$ be natural numbers, let $x, y, p, q \in R$, and write $[a, b]_{p,q}$ for the
$(p, q)$-binomial coefficients. The first-kind $(p, q)$-analogue $V^{(r,s)}_n(x, y, p, q, m)$ of
the $r$-Lucas polynomial of type $s$, written $V_n$, is defined by $V_0 = s + 1$ and, for
$n \ge 1$,

$$
V_n = \sum_{k=0}^{\lfloor n/(r+1) \rfloor} p^{\binom{n-(r+1)k}{2}} q^{(m+1)\binom{k}{2}}\,
c_{n,k}\,x^{n-(r+1)k} y^k,
$$

where $c_{n,0} = [n, 0]_{p,q}$ and, for $k \ge 1$,
$c_{n,k} = [n - rk, k]_{p,q} + s\,p^{n-(r+1)k} [n - rk - 1, k - 1]_{p,q}$.

The paper writes $c_{n,k}$ as
$[n - rk, k]_{p,q} (1 + s\,p^{n-(r+1)k} [k]_{p,q} / [n - rk]_{p,q})$, with $[a]_{p,q}$ the
$(p, q)$-numbers; the division-free form is the first step of the paper's proof of Theorem 3
and agrees with it whenever $[n - rk]_{p,q} \ne 0$.

## Sources

- Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025), Article A38, Definition 2.
