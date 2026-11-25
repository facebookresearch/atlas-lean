# In the simple cubic lattice, a direction is normal to its own planes

Let $\Lambda$ be the simple cubic lattice of side $a > 0$, with basis matrix $B = aI$ (primitive
vectors $a e_0, a e_1, a e_2$). Its crystallographic reciprocal basis $b_0, b_1, b_2$ consists of
the columns of $(B^{-1})^{\mathsf T}$ (no factor $2\pi$). For integer indices $h = (h_0, h_1, h_2)$,
the reciprocal vector is $G_h = \sum_j h_j b_j$. The lattice direction $[u]$ for integer $u$ is
$\sum_j u_j a_j$. Then $[h] = a^2 G_h$, so for $h \ne 0$ the direction $[h]$ is normal to the
[planes](lattice-plane.md) $G_h \cdot x = n$ of the family $h$.
