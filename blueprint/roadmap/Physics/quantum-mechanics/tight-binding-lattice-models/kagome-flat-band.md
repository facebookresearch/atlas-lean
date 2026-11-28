# Kagome flat band

For $t \ne 0$ the nearest-neighbour kagome model has an exactly flat band at energy $2t$, touched at the zone centre by a dispersive band.

For the kagome model with real hopping $t \ne 0$, lattice vectors $a_1, a_2, a_3 = -a_1 - a_2$ and sublattice basis
$s_1 = 0$, $s_2 = a_1/2$, $s_3 = -a_2/2$ as in its definition, let

$$
h(q) = -t\begin{pmatrix}
0 & 1 + e^{-iq\cdot a_1} & 1 + e^{iq\cdot a_2} \\
1 + e^{iq\cdot a_1} & 0 & 1 + e^{-iq\cdot a_3} \\
1 + e^{-iq\cdot a_2} & 1 + e^{iq\cdot a_3} & 0
\end{pmatrix},
$$

which is periodic under the reciprocal lattice. Per spin, writing $\psi$ through its values $\psi_\mu(R)$ at
$R + s_\mu$, the Fourier transform over $\Lambda$ makes the model unitarily equivalent to multiplication by $h(q)$ on the
reciprocal torus, and the eigenvalues of $h(q)$ are

$$
\epsilon_0(q) = 2t, \qquad \epsilon_\pm(q) = -t\left(1 \pm \sqrt{3 + 2\Lambda(q)}\right),
\qquad \Lambda(q) = \sum_{\mu=1}^{3}\cos(q\cdot a_\mu),
$$

with $3 + 2\Lambda(q) = |1 + e^{iq\cdot a_1} + e^{-iq\cdot a_2}|^2 \in [0, 9]$. The band $\epsilon_-$ meets the flat band
at the $\Gamma$ point $q = 0$; the flat band is the top of the spectrum for $t > 0$ and the bottom for $t < 0$. These are
bands of the infinite periodic operator (or its values at allowed momenta on a periodic finite torus), not eigenvalues
of an open finite fragment.

## Context

Research level. A half-filled flat band of this kind is the design target of kagome metal–organic frameworks proposed for flat-band ferromagnetism.

## Depends on

- [Kagome nearest-neighbour tight-binding model](kagome-nearest-neighbour-tight-binding-model.md)

## Proof depends on

None.

## Expansion

Each site has two neighbours of each other sublattice, in the cells given by the phases of $h(q)$. With
$D(q) = \mathrm{diag}(e^{iq\cdot s_\mu})$, the pointwise conjugation $D(q)^\ast h(q)D(q)$ is $-2t$ times the symmetric
matrix with off-diagonal entries $c_1, c_2, c_3$, $c_\mu = \cos(q\cdot a_\mu/2)$, in positions $(1,2)$, $(1,3)$, $(2,3)$;
this position-gauge form is not periodic on the torus but has the same eigenvalues. Since the half-angles sum to zero,
$c_1^2 + c_2^2 + c_3^2 = 1 + 2c_1c_2c_3$, so the cosine matrix has characteristic polynomial
$\lambda^3 - (1 + 2p)\lambda - 2p = (\lambda + 1)(\lambda^2 - \lambda - 2p)$ with $p = c_1c_2c_3$; multiplying the roots by
$-2t$ and using $1 + 8p = 3 + 2\Lambda$ gives the three bands. At $q = 0$, $\Lambda = 3$ and $\epsilon_-(0) = 2t$. The
operator-level statement needs the Fourier unitary reducing a finite-range periodic hopping operator on
$\ell^2(\Lambda;\mathbb{C}^3)$ to multiplication by its periodic Bloch matrix, a prerequisite not yet in the graph.

## Sources

- D. L. Bergman, C. Wu and L. Balents, "Band touching from real-space topology in frustrated hopping models", *Physical Review B* 78, 125104 (2008), [doi.org](https://doi.org/10.1103/PhysRevB.78.125104); equation numbers from arXiv:0803.3628v2, Section II.A, Eq. (2).
