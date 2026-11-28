# Honeycomb tight-binding bands

The nearest-neighbour honeycomb model has the two bands $E_\pm(k) = \pm t\sqrt{3 + f(k)}$, the eigenvalues of its $2\times2$ Bloch matrix.

For the honeycomb model with hopping $t > 0$ and nearest-neighbour distance $a > 0$, let
$g_{\mathrm{per}}(k) = 1 + e^{ik\cdot a_1} + e^{ik\cdot a_2}$, which is periodic under the reciprocal lattice $\Lambda^\ast$, and

$$
h(k) = \begin{pmatrix} 0 & -t\,g_{\mathrm{per}}(k) \\ -t\,\overline{g_{\mathrm{per}}(k)} & 0 \end{pmatrix}, \qquad
f(k) = 2\cos\!\left(\sqrt{3}k_ya\right) + 4\cos\!\left(\tfrac{\sqrt{3}}{2}k_ya\right)\cos\!\left(\tfrac{3}{2}k_xa\right).
$$

Per spin, writing $\psi$ through its values $\psi_A(R)$ at $R$ and $\psi_B(R)$ at $R + \delta_3$ for $R \in \Lambda$, the
Fourier transform over $\Lambda$ makes the model unitarily equivalent to multiplication by $h(k)$ on
$L^2(\mathbb{R}^2/\Lambda^\ast;\mathbb{C}^2)$, and the eigenvalues of $h(k)$ are

$$
E_\pm(k) = \pm t\,|g_{\mathrm{per}}(k)| = \pm t\sqrt{3 + f(k)},
$$

the two energy bands, symmetric about zero and equal (to $0$) exactly where $g_{\mathrm{per}}(k) = 0$. The source's symbol
$g(k) = \sum_j e^{ik\cdot\delta_j} = e^{ik\cdot\delta_3}g_{\mathrm{per}}(k)$ differs by a pointwise phase (a position gauge)
and gives the same bands, but is not periodic on the torus. These are bands of the infinite periodic operator (or, on a
periodic finite torus, its values at the allowed momenta), not eigenvalues of an open finite piece of the lattice.

## Context

Graduate level. The two-band, electron–hole-symmetric spectrum is the reference against which computed band structures of honeycomb conductive MOFs are compared.

## Depends on

- [Honeycomb nearest-neighbour tight-binding model](honeycomb-nearest-neighbour-tight-binding-model.md)

## Proof depends on

None.

## Expansion

The $A$ site at $R$ has its $B$ neighbours in the cells $R$, $R + a_1$, $R + a_2$, so on cell-periodic Bloch data
$\psi_\mu(R) = e^{ik\cdot R}u_\mu$ the operator acts by $h(k)$. The Hermitian matrix $h(k)$ with zero diagonal has
eigenvalues $\pm t|g_{\mathrm{per}}(k)|$, and $|g_{\mathrm{per}}|^2 = 3 + 2\cos(k\cdot a_1) + 2\cos(k\cdot a_2) + 2\cos(k\cdot(a_1 - a_2))$,
which equals $3 + f(k)$ since $a_1 - a_2 = (0, \sqrt3a)$. The operator-level statement needs a prerequisite not yet in the
graph: the Fourier unitary that conjugates lattice translations to characters, reducing a finite-range periodic hopping
operator on $\ell^2(\Lambda;\mathbb{C}^m)$ to multiplication by its periodic Bloch matrix on the reciprocal torus.

## Sources

- A. H. Castro Neto, F. Guinea, N. M. R. Peres, K. S. Novoselov and A. K. Geim, "The electronic properties of graphene", *Reviews of Modern Physics* 81, 109–162 (2009), [doi.org](https://doi.org/10.1103/RevModPhys.81.109); equation numbers from arXiv:0709.1163v2, Eq. (6) with $t' = 0$ and Eq. (16) (Fourier convention).
