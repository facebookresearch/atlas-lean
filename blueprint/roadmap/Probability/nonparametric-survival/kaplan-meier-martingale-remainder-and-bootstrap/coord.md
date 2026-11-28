# Indicator coordinate space for the grid Kaplan–Meier bootstrap

For $k \in \mathbb N$, the indicator coordinate space is the Euclidean space

$$\mathbb R^{I}, \qquad I = \{\mathrm{death}, \mathrm{risk}\} \times \{0, \dots, k - 1\},$$

of dimension $2k$, with the Euclidean ($\ell^2$) norm and inner product. The coordinates come in two copies of the index $j \in \{0, \dots, k - 1\}$: the death coordinate $(\mathrm{death}, j)$ and the at-risk coordinate $(\mathrm{risk}, j)$. The [indicator encoding](obs-vec.md) of an observation on a grid $t_0, \dots, t_{k-1}$ puts the death indicator at $t_j$ in the death coordinate $(\mathrm{death}, j)$ and the at-risk indicator at $t_j$ in the at-risk coordinate $(\mathrm{risk}, j)$.
