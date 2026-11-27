# Zig-zag product of rotation maps

Let $G$ be a [rotation map](rotation-map.md) on $V \times K$ and $H$ a rotation map on $K \times L$. The zig-zag product $G \circledcirc H$ is the rotation map on $(V \times K) \times (L \times L)$ given by

$$\mathrm{rot}\big((v, k), (i, j)\big) = \big((w, l), (j', i')\big),$$

where $(k', i') = \mathrm{rot}_H(k, i)$, $(w, l') = \mathrm{rot}_G(v, k')$ and $(l, j') = \mathrm{rot}_H(l', j)$: a step in the small graph $H$, a step in the big graph $G$ along the resulting label, and a second step in $H$ (O. Reingold, S. Vadhan and A. Wigderson, Ann. of Math. 155 (2002), Definition 3.1). If $G$ is $\lvert K\rvert$-regular on $N$ vertices and $H$ is $\lvert L\rvert$-regular on $\lvert K\rvert$ vertices, $G \circledcirc H$ is $\lvert L\rvert^2$-regular on $N \lvert K\rvert$ vertices.
