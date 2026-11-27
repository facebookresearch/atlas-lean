# Continued-fraction denominators

Given a power series $B$ in $x$ over $\mathbb{Z}[q]$,
define power series $K_k$ in $x$ over $\mathbb{Z}[q]$ by $K_0 = 1$, $K_1 = B$ and, for $k \ge 2$,
$K_k = 1 - q^k x - q^{2k-1} x^2 K_{k-1}^{-1}$. Here $K_{k-1}^{-1}$ is the formal inverse of
$K_{k-1}$ computed with constant term $1$. It is the true inverse whenever $K_{k-1}$ has constant
term $1$, which always holds for $k \ge 3$, and for $k = 2$ when $B$ has constant term $1$.
Lemma 8 takes $B = 1 - qx$ and Lemma 10 takes $B = 1$; the value $K_0$ is unused.

## Sources

- Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According to Capacity*, INTEGERS 25 (2025), Article A5, Lemmas 8 and 10.
