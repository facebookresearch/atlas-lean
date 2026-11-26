# Square of a rotation map

For a [rotation map](rotation-map.md) $\mathrm{rot}$ on $V \times L$, the square $G^2$ is the rotation map on $V \times (L \times L)$ given by

$$\mathrm{rot}_{G^2}(v, (i, j)) = (u, (j', i')), \qquad \text{where } (w, i') = \mathrm{rot}(v, i),\ (u, j') = \mathrm{rot}(w, j):$$

it has an edge labelled $(i, j)$ from $v$ to $u$ for every two-step walk $v \to w \to u$ that leaves $v$ along label $i$ and $w$ along label $j$ (O. Reingold, S. Vadhan and A. Wigderson, Ann. of Math. 155 (2002), Section 2.3, the $t$-th power with $t = 2$).
