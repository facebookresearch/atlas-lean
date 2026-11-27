# Two finite expansions of the Eulerian polynomials

Let $A(n,k)$ be the Eulerian numbers,
given by $A(0,0) = 1$, $A(0,k) = 0$ for $k \ge 1$ and
$A(n+1,k) = (k+1)A(n,k) + (n+1-k)A(n,k-1)$, where the last term is $0$ when $k = 0$, and let
$\Psi_0(p) = 1$ and $\Psi_n(p) = \sum_{k=0}^{n-1} A(n,k)(-p)^k$ for $n \ge 1$. For every integer
$n \ge 1$ and every complex number $p \ne -1$, we have $p + 1 \ne 0$, $\Psi_0(p) = 1$,
$(-1)^{n+1} p \, \Psi_n(p)/(p+1)^n = \sum_{k=0}^{n} (-1)^k \binom{n}{k} \Psi_k(p)/(p+1)^k$, and
$\Psi_n(p) = \sum_{j=0}^{n-1} (-1)^j \binom{n}{j+1} (p+1)^j \Psi_{n-j-1}(p)$.

## Sources

- Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 5, Entry 5, formulas (5.1) and (5.2).
