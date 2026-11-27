# Translation-invariant nearest-neighbor lattice Hamiltonians

A translation-invariant nearest-neighbor Hamiltonian on a square lattice or a chain is fixed by finitely many matrices: one on-site term and one interaction per lattice direction, repeated over every site and bond, giving one Hamiltonian for each nonempty system size.

**Lattices and Hilbert spaces.** Fix a local dimension $d\ge2$, so that every system below has at least two energy levels. Let $\Lambda(L)$ be either the $L\times L$ square lattice $\{1,\dots,L\}^2\subset\mathbb Z^2$ for a side length $L\in\mathbb N$ with $L\ge2$, as in the source, or the chain $\{1,\dots,L\}$ for a length $L\ge1$, with *open boundary conditions*: the bonds $\mathcal E$ join lattice neighbors inside $\Lambda(L)$ and do not wrap around. Each site $k$ carries a copy $\mathcal H^{(k)}\cong\mathbb C^d$, and the system lives on $\bigotimes_{k\in\Lambda(L)}\mathcal H^{(k)}$.

**Interactions.** A *translation-invariant nearest-neighbor Hamiltonian* on the square lattice is given by a Hermitian $d\times d$ matrix $h_1$ and Hermitian $d^2\times d^2$ matrices $h_{\mathrm{row}}$ and $h_{\mathrm{col}}$, and is the family

$$
H^{\Lambda(L)}=\sum_{\text{rows}}\sum_{c}h_{\mathrm{row}}^{(c,c+1)}+\sum_{\text{columns}}\sum_{r}h_{\mathrm{col}}^{(r,r+1)}+\sum_{k\in\Lambda(L)}h_1^{(k)},\qquad L\ge2,
$$

where $h^{(i,j)}$ acts as the given matrix on the sites $i,j$ and as the identity elsewhere, and $h_1^{(k)}$ likewise on site $k$. On a chain there is a single two-site matrix $h^{(2)}$ and

$$
H_N=\sum_{i=1}^{N-1}h^{(2)}_{i,i+1}+\sum_{i=1}^{N}h^{(1)}_i ,\qquad N\ge1 .
$$

The same matrices are used at every site, bond and system size. The *local interaction strength* is $\max\{\|h_{\mathrm{row}}\|,\|h_{\mathrm{col}}\|,\|h_1\|\}$ (operator norm).

**Spectral quantities.** The eigenvalues of $H^{\Lambda(L)}$ are listed with multiplicity in non-decreasing order $\lambda_0\le\lambda_1\le\cdots$; $\lambda_0$ is the *ground-state energy*, and the *spectral gap* is

$$
\Delta(H^{\Lambda(L)})=\lambda_1(H^{\Lambda(L)})-\lambda_0(H^{\Lambda(L)}).
$$

On the square lattice the *ground-state energy density* is

$$
E_\rho=\lim_{L\to\infty}\frac{\lambda_0(H^{\Lambda(L)})}{L^2},
$$

and the limit exists. The Hamiltonian is *frustration-free* if all interaction terms are positive semidefinite and $\lambda_0(H^{\Lambda(L)})=0$, and *classical* if all interaction terms are diagonal in a fixed product basis.

## Depends on

- [Hypercubic lattice $\mathbb{Z}^d$](../../../../GraphTheory/graph-families-and-operations/hypercubic-lattice-graphs/hypercubic-lattice.md)

## Proof depends on

None.

## Sources

- T. Cubitt, D. Perez-Garcia and M. M. Wolf, "Undecidability of the spectral gap", *Forum of Mathematics, Pi* 10, e14, 2022, doi:[10.1017/fmp.2021.15](https://doi.org/10.1017/fmp.2021.15); read in arXiv:1502.04573v5 ([arXiv](https://arxiv.org/abs/1502.04573v5)), whose numbering is used: Section 1.1, "Definitions and notation" (lattice of side $L\ge2$, interactions, local interaction strength, energy levels, ground-state energy density, frustration-free and classical Hamiltonians, spectral gap).
- J. Bausch, T. S. Cubitt, A. Lucia and D. Perez-Garcia, "Undecidability of the spectral gap in one dimension", *Physical Review X* 10(3), 031038, 2020, doi:[10.1103/PhysRevX.10.031038](https://doi.org/10.1103/PhysRevX.10.031038); read in arXiv:1810.01858v2 ([arXiv](https://arxiv.org/abs/1810.01858v2)): the definition of the chain Hamiltonian $H_N$, eq. (1), in the introduction.
