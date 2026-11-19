# Eulerian polynomials at 1 and -1 and two series for 1/(e^z + 1)

Let $A(n,k)$ be the
Eulerian numbers, given by $A(0,0) = 1$, $A(0,k) = 0$ for $k \ge 1$ and
$A(n+1,k) = (k+1)A(n,k) + (n+1-k)A(n,k-1)$, where the last term is $0$ when $k = 0$; let
$\Psi_0(p) = 1$ and $\Psi_n(p) = \sum_{k=0}^{n-1} A(n,k)(-p)^k$ for $n \ge 1$, and let $B_m$ be
the Bernoulli numbers, with $B_1 = -\tfrac{1}{2}$. For every integer $n \ge 1$ and every complex
number $z$ with $|z| < \pi$, we have $e^z + 1 \ne 0$, $\Psi_n(-1) = n!$,
$\Psi_n(1) = 2^{n+1}(2^{n+1} - 1)B_{n+1}/(n+1)$, the series
$\sum_{j \ge 0} (1 - 2^{j+1}) B_{j+1} z^j/(j+1)!$ is summable with sum $1/(e^z + 1)$, and the
series $\sum_{m \ge 0} (-1)^m \Psi_m(1) z^m/(2^{m+1} m!)$ is summable with sum $1/(e^z + 1)$.

## Sources

- Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 5, Entry 8.
