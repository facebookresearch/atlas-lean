# Approximate near neighbours in l2 and l1 by p-stable LSH

For $p \in \{1, 2\}$, every bucket width $w > 0$, radius $r > 0$ and approximation $c > 1$, the collision probability $p_w(\delta)$ of the $p$-stable hash is strictly positive and strictly decreasing in $\delta \ge 0$, so with $p_1 = p_w(r)$ and $p_2 = p_w(cr)$ we have $0 < p_2 < p_1 \le 1$ and LSH exponent $\rho < 1$. Consequently the LSH index with $k$ AND-composed $p$-stable hashes, $L$ tables and stopping rule $T = 3L$ answers $(c, r)$-approximate near-neighbour queries in $(\mathbb{R}^d, \ell_p)$ with failure probability at most $e^{-1} + 1/3$, using $L = O(n^\rho)$ tables for a sublinear exponent $\rho < 1$.

## Proof sketch

For $p$-stable $\nu$ with symmetric unimodal density $f$, $p_w(\delta) = \int_0^w \frac{2}{\delta} f(t/\delta)(1 - t/w)\, dt$ for $\delta > 0$ (the factor $2$ comes from the density $\frac{2}{\delta}f(t/\delta)$ of $|\langle a, x - y\rangle|$), which is positive and strictly decreasing in $\delta$. Strict monotonicity gives $p_2 < p_1$ and hence $\rho < 1$, and the failure bound is the general LSH bound for measurable seed laws.

## Depends on

- [p-stable locality-sensitive hash family](p-stable-lsh-family.md)

## Proof depends on

- [Failure probability of the LSH index](failure-probability-of-the-lsh-index.md)

## Sources

- M. Datar, N. Immorlica, P. Indyk and V. S. Mirrokni, "Locality-Sensitive Hashing Scheme Based on p-Stable Distributions", Proceedings of the 20th Symposium on Computational Geometry (SoCG), 2004.
- S. Har-Peled, P. Indyk and R. Motwani, "Approximate Nearest Neighbor: Towards Removing the Curse of Dimensionality", Theory of Computing 8(14), 2012.
