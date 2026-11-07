# The residue walk $\tilde g_l$

For natural numbers $p$ and $l$, write
$\left(\frac{a}{p}\right)$ for the Jacobi symbol. The residue walk
$\tilde g_l \colon \mathbb{N} \to \mathbb{N}$ of $p$ starting at $l$ is defined by
$\tilde g_l(0) = 0$, $\tilde g_l(1) = l$ and, for every $n \ge 1$,
$\tilde g_l(n+1) = \tilde g_l(n) + \left(\frac{n}{p}\right)\left(\frac{\tilde g_l(n)}{p}\right)$
if $0 < \tilde g_l(n) < p$, and $\tilde g_l(n+1) = \tilde g_l(n)$ otherwise.

The sum in the first case is never negative, since $\tilde g_l(n) \ge 1$ there. The paper only
uses the indices $1 \le n \le p$; the value at $0$ and the values beyond $p$ totalize the walk.
For an odd prime $p$ the Jacobi symbol is the Legendre symbol.

## Sources

- Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 29 (2026), Article 26.3.8, Section 2 definition of `tilde g_l`.
