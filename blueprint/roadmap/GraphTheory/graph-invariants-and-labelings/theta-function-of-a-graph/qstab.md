# Clique-constrained stable set polytope

For a finite graph $G$ on $V$,

$$
\mathrm{QSTAB}(G) = \Bigl\{x \in \mathbb{R}^V : x \ge 0,\ \sum_{v \in Q} x_v \le 1 \text{ for every clique } Q \text{ of } G\Bigr\}.
$$

Every stable set meets every clique in at most one vertex, so $\mathrm{STAB}(G) \subseteq \mathrm{QSTAB}(G)$; the two are equal exactly for perfect graphs ([STAB = QSTAB characterises perfect graphs](is-perfect-iff-stab-eq-qstab.md)). Maximising $\sum_v x_v$ over it gives the fractional clique cover number.

## Sources

- D. E. Knuth, *The Sandwich Theorem*, Electron. J. Combin. 1 (1994), #A1, arXiv:math/9312214v1, §2 and eq. (4.8).
