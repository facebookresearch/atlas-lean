# Thresholds for bounded-degree spanning trees and spanning graphs

For every $\Delta$, the threshold for $G(n, p)$ to contain a given spanning tree $T$ of maximum degree at most $\Delta$ is $O_\Delta(\log n / n)$ (Montgomery's theorem, reproved via spreadness), and for every $n$-vertex graph $H$ with at least two edges the threshold for containing a copy of $H$ is at most $O(\log n)$ times its expectation threshold $q$, with a universal implied constant.

## Proof sketch

Construct a $\kappa$-spread distribution on embeddings of $T$ into $K_n$ with $\kappa = \Omega_\Delta(n)$, for instance a uniformly random bijection, for which any fixed set of $t$ edges of $K_n$ is contained in the image with probability at most $(C_\Delta/n)^{t}$. Apply the fractional expectation-threshold theorem with $\ell = n - 1$. For the second claim, the family of graphs on $[n]$ containing a copy of $H$ has minimal elements with at most $\binom{n}{2}$ edges, so the Park-Pham theorem bounds its threshold by $K\,q\log\binom{n}{2} = O(q\log n)$.

## Depends on

- [The Kahn-Kalai expectation threshold q(F)](kahn-kalai-expectation-threshold.md)

## Proof depends on

- [Thresholds versus fractional expectation-thresholds](../thresholds-and-expectation-thresholds/theorem-1-1.md)
- [Spread families and spread measures](../../extremal-set-theory/spread-families-and-robust-sunflowers/kappa-spread-families-and-measures.md)
- [Park-Pham theorem: thresholds are within a logarithmic factor of expectation thresholds](park-pham-theorem.md)

## Sources

- Keith Frankston, Jeff Kahn, Bhargav Narayanan, Jinyoung Park, "Thresholds versus fractional expectation-thresholds", Annals of Mathematics 194(2) (2021); arXiv:1910.13433, Theorems 1.1 and 7.1.
- Jinyoung Park, Huy Tuan Pham, "A proof of the Kahn-Kalai conjecture", Journal of the AMS 37(1) (2024); arXiv:2203.17207, Theorem 1.1.
- Richard Montgomery, "Spanning trees in random graphs", Advances in Mathematics 356 (2019).
