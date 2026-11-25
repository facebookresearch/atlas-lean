# Reciprocal lattice

Let $\Lambda$ be a Bravais lattice with basis matrix $B$ ($\det B \ne 0$), primitive vectors
$a_0, a_1, a_2$ (the columns of $B$) and lattice $L = \{Bn : n \in \mathbb{Z}^3\}$. Its reciprocal
lattice is the Bravais lattice with basis matrix $(2\pi/V)\,X(B)$, where $V = \det B$ and $X(B)$ is
the [matrix of cross products](cross-columns.md) of the columns of $B$; its primitive vectors are
$b_0 = \tfrac{2\pi}{V}(a_1 \times a_2)$, $b_1 = \tfrac{2\pi}{V}(a_2 \times a_0)$ and
$b_2 = \tfrac{2\pi}{V}(a_0 \times a_1)$. This is the physics convention
$a_i \cdot b_j = 2\pi\delta_{ij}$ ([duality](inner-primitive-vector-reciprocal.md)), not the
crystallographic one without the factor $2\pi$.
