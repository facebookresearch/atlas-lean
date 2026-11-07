# Eulerian polynomials and the series of (k+1)^n (-p)^k

Let $A(n,k)$ be the Eulerian
numbers, given by $A(0,0) = 1$, $A(0,k) = 0$ for $k \ge 1$ and
$A(n+1,k) = (k+1)A(n,k) + (n+1-k)A(n,k-1)$, where the last term is $0$ when $k = 0$, and let
$\Psi_0(p) = 1$ and $\Psi_n(p) = \sum_{k=0}^{n-1} A(n,k)(-p)^k$ for $n \ge 1$. For every natural
number $n$ and every complex number $p$ with $|p| < 1$, we have $p + 1 \ne 0$, the series
$\sum_{k \ge 0} (k+1)^n (-p)^k$ is summable, and
$\Psi_n(p)/(p+1)^{n+1} = \sum_{k=0}^{\infty} (k+1)^n (-p)^k$.

## Sources

- Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 5, Entry 4, p. 113. Proves `Wanted` entry `ramanujan_part1_ch5_entry4`.
