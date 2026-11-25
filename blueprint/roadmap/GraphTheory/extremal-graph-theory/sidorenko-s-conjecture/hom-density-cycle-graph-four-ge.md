# Sidorenko's inequality for the four-cycle

For every weighted graph $w$ on a finite vertex set,

$$t(C_4, w) \ge t(K_2, w)^4 .$$

With $M(a, c) = \sum_b w(a, b) w(b, c)$ and the degrees $d(b) = \sum_a w(a, b)$, two applications of the Cauchy–Schwarz inequality give

$$\sum_{a,b,c,d} w(ab) w(bc) w(cd) w(da) = \sum_{a, c} M(a, c)^2 \ge \frac{1}{n^2} \Big( \sum_b d(b)^2 \Big)^2 \ge \frac{1}{n^4} \Big( \sum_{a, b} w(ab) \Big)^4 .$$

No sign condition on $w$ is needed. This is the case $F = C_4 = K_{2,2}$ of Sidorenko's conjecture.

## Background

- [Sidorenko's conjecture](sidorenko-conjecture.md): the general statement for bipartite $F$.
- [Homomorphism density](../../random-graphs/graph-limits/hom-density.md): the densities compared.

## Sources

- L. Lovász, "Subgraph densities in signed graphons and the local Sidorenko conjecture", arXiv:1004.3026v1 (2010); published in *Electron. J. Combin.* 18 (2011), §1, inequality (1) and the known cases (bigraphs with a colour class of at most four nodes).
