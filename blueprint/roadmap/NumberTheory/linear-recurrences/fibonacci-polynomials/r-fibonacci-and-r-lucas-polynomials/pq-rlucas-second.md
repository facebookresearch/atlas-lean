# Second-kind (p, q)-Lucas polynomials

Let $K$ be a field, let $r$, $s$ and $m$ be natural
numbers, let $x, y, p, q \in K$, and write $[a, b]_{p,q}$ for the $(p, q)$-binomial
coefficients. The second-kind $(p, q)$-analogue $\mathbb{V}^{(r,s)}_n(x, y, p, q, m)$ of the
$r$-Lucas polynomial of type $s$, written $\mathbb{V}_n$, is defined by $\mathbb{V}_0 = s + 1$
and, for $n \ge 1$,

$$
\mathbb{V}_n = \sum_{k=0}^{\lfloor n/(r+1) \rfloor}
\frac{p^{\binom{n-(r+1)k}{2}} q^{\binom{k+1}{2} + m\binom{k}{2}}}{p^k}\,
d_{n,k}\,x^{n-(r+1)k} y^k,
$$

where $d_{n,0} = [n, 0]_{p,q}$ and, for $k \ge 1$,
$d_{n,k} = [n - rk, k]_{p,q} + s\,q^{n-(r+1)k} [n - rk - 1, k - 1]_{p,q}$. Division by $0$ is
read as $0$, so for $p = 0$ every term with $k \ge 1$ vanishes.

The paper writes $d_{n,k}$ as
$[n - rk, k]_{p,q} (1 + s\,q^{n-(r+1)k} [k]_{p,q} / [n - rk]_{p,q})$, with $[a]_{p,q}$ the
$(p, q)$-numbers; the two agree whenever $[n - rk]_{p,q} \ne 0$.

## Sources

- Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025), Article A38, Definition 2.
