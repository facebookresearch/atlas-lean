# Honeycomb nearest-neighbour tight-binding model

The honeycomb tight-binding model is the one-particle operator $-t$ times the adjacency operator of the honeycomb lattice, two sites per unit cell, with real hopping $t$.

Let $a > 0$ be the nearest-neighbour distance, $\Lambda$ the triangular Bravais lattice spanned by
$a_1 = \tfrac{a}{2}(3, \sqrt{3})$ and $a_2 = \tfrac{a}{2}(3, -\sqrt{3})$, and
$\delta_1 = \tfrac{a}{2}(1, \sqrt{3})$, $\delta_2 = \tfrac{a}{2}(1, -\sqrt{3})$, $\delta_3 = -a(1, 0)$. The honeycomb
lattice has sublattices $A = \Lambda$ and $B = \Lambda + \delta_3$, and each $A$ site $R$ is joined to the three $B$ sites
$R + \delta_j$ (note $\delta_1 - \delta_3 = a_1$, $\delta_2 - \delta_3 = a_2$). For a real hopping energy $t$, the
nearest-neighbour tight-binding model for one spin is the operator on the complex Hilbert space $\ell^2(A \cup B)$

$$
(H\psi)(v) = -t\sum_{u \sim v} \psi(u),
$$

the sum running over the three nearest neighbours $u$ of $v$. It is bounded with $\|H\| \le 3|t|$ and self-adjoint. On
a finite set of sites with the induced bonds the matrix of the compression of $H$ is the Hückel matrix of that graph with
$\alpha = 0$ and $\beta = -t$.

## Context

Graduate level. Fully π–d conjugated 2D MOFs such as Ni3(HITP)2 are called metal–organic graphene analogues; the honeycomb model is a caricature of their electronic structure, not an identification. The source writes the model in second-quantized notation, −t Σ (a†b + h.c.) summed over spins and bonds; here it is used only as the one-particle operator above. For reference, the reciprocal lattice is spanned by b1,2 = (2π/3a)(1, ±√3), with zone corners K, K′ = (2π/3a, ±2π/(3√3 a)).

## Depends on

- [Hückel matrix of a graph](../../../Chemistry/quantum-chemistry-and-spectroscopy/variational-method-perturbation-theory-and-h-cke/huckel-matrix.md)

## Proof depends on

- [Schur's test](../../../Analysis/operator-theory/integral-and-multiplication/schur-test/norm-schur-inf-operator-le.md)

## Expansion

Enumerating the countable vertex set by $\mathbb{N}$, $H$ is the matrix with entries $-t$ on adjacent pairs and $0$
elsewhere; every row and every column has absolute sum $3|t|$, so Schur's test gives $\|H\| \le 3|t|$. The matrix is real
and symmetric because adjacency is undirected and $t$ is real, so $H$ is symmetric on finitely supported vectors and,
being bounded, self-adjoint. The source also includes a next-nearest-neighbour hopping $t'$, set to zero here. The Hückel
dependency concerns only the finite compression, not the infinite periodic operator.

## Sources

- A. H. Castro Neto, F. Guinea, N. M. R. Peres, K. S. Novoselov and A. K. Geim, "The electronic properties of graphene", *Reviews of Modern Physics* 81, 109–162 (2009), [doi.org](https://doi.org/10.1103/RevModPhys.81.109); equation numbers from arXiv:0709.1163v2, Eqs. (1)–(5) with $t' = 0$, and Fig. 2.
- D. Sheberla, L. Sun, M. A. Blood-Forsythe, S. Er, C. R. Wade, C. K. Brozek, A. Aspuru-Guzik and M. Dincă, "High electrical conductivity in Ni3(2,3,6,7,10,11-hexaiminotriphenylene)2, a semiconducting metal–organic graphene analogue", *Journal of the American Chemical Society* 136 (2014), [doi.org](https://doi.org/10.1021/ja502765n), title and abstract (the graphene-analogue description).
