# Kagome nearest-neighbour tight-binding model

The kagome tight-binding model is the one-particle operator $-t$ times the adjacency operator of the kagome lattice, three sites per unit cell.

Let $a_1, a_2 \in \mathbb{R}^2$ have equal length $2\ell > 0$ and enclose an angle of $120^\circ$, let
$a_3 = -a_1 - a_2$, and let $\Lambda$ be the triangular Bravais lattice they span. The kagome lattice is the set of sites
$\Lambda \cup (\Lambda + a_1/2) \cup (\Lambda - a_2/2)$, two sites being nearest neighbours when their distance is
$\ell$; each site has four neighbours and the bonds form corner-sharing triangles. For each spin the nearest-neighbour
tight-binding model with real hopping $t$ is the bounded self-adjoint operator on $\ell^2$ of the sites

$$
(H\psi)(v) = -t\sum_{u \sim v} \psi(u),
$$

equivalently $H_0 = -t\sum_{\langle ij\rangle,\sigma}(c^\dagger_{i\sigma}c_{j\sigma} + \mathrm{h.c.})$ with each bond counted
once. On a finite set of sites with the induced bonds the matrix of $H$ is the Hückel matrix of that graph with
$\alpha = 0$ and $\beta = -t$. Further-neighbour hopping, spin–orbit coupling and Zeeman terms are added to $H_0$ when
fitting real materials.

## Context

Research level. Yamada, Soejima, Tsuji, Hirai, Dincă and Aoki predicted from first-principles calculations 2D MOFs whose frontier bands are fitted by this model, with the Fermi level at an approximately half-filled, nearly flat band; this is a computational design, not an experimental realization of an exactly flat band.

## Depends on

- [Hückel matrix of a graph](../../../Chemistry/quantum-chemistry-and-spectroscopy/variational-method-perturbation-theory-and-h-cke/huckel-matrix.md)

## Proof depends on

None.

## Expansion

The basis displacements $a_1/2$, $-a_2/2$ and their difference $a_3/2$ (up to sign) all have length $\ell$, which gives
the nearest-neighbour bonds. The Hückel dependency concerns only the finite restriction.

## Sources

- M. G. Yamada, T. Soejima, N. Tsuji, D. Hirai, M. Dincă and H. Aoki, "First-principles design of a half-filled flat band of the kagome lattice in two-dimensional metal-organic frameworks", *Physical Review B* 94, 081102(R) (2016), [doi.org](https://doi.org/10.1103/PhysRevB.94.081102); equation numbers from arXiv:1510.00164v3, Eq. (1) with $t_1 = t$ and $t_2 = 0$, and Fig. 1(c).
- D. L. Bergman, C. Wu and L. Balents, "Band touching from real-space topology in frustrated hopping models", *Physical Review B* 78, 125104 (2008), [doi.org](https://doi.org/10.1103/PhysRevB.78.125104); equation numbers from arXiv:0803.3628v2, Eq. (1) and Fig. 1.
