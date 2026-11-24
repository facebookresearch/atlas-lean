# Stable set polytope

For a finite graph $G$ on $V$, the stable set polytope is

$$
\mathrm{STAB}(G) = \operatorname{conv}\{\chi^S : S \subseteq V \text{ stable in } G\} \subseteq \mathbb{R}^V ,
$$

the convex hull of the [characteristic vectors](char-vec.md) of the stable sets. Maximising $\sum_v x_v$ over it gives the independence number $\alpha(G)$.

## Sources

- D. E. Knuth, *The Sandwich Theorem*, Electron. J. Combin. 1 (1994), #A1, arXiv:math/9312214v1, §2 and eq. (4.7).
