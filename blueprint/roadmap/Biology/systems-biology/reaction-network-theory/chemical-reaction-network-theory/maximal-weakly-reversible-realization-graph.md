# Maximal weakly reversible realization graph

Let $G = (V,E)$ be an E-graph (a finite simple directed graph with vertices in $\mathbb{Z}^n$) generating mass-action systems, and let $G^{\mathrm{comp}}$ be the complete simple directed graph on the source vertices of $G$. Say $G$ *admits a realization with respect to* an E-graph $H$ if $(G,\kappa)$ and $(H,\lambda)$ are dynamically equal (same mass-action vector field) for some positive $\kappa,\lambda$. Let $\mathcal{H}_{\mathrm{wr}}(G)$ be the set of weakly reversible subgraphs $H \subseteq G^{\mathrm{comp}}$ for which $G$ admits a realization with respect to $H$. For a fixed $H$, $\mathcal{K}_{\mathrm{disg}}(G,H)$ denotes the rate constants $\kappa$ for which $(G,\kappa)$ is dynamically equal to a vertex-balanced (complex-balanced) system on $H$, and $\mathcal{F}_{\mathrm{disg}}(G,H)$ the analogous set of fluxes.

**Facts.** $\mathcal{K}_{\mathrm{disg}}(G,H) \ne \emptyset$ if and only if $H \in \mathcal{H}_{\mathrm{wr}}(G)$, and $\mathcal{H}_{\mathrm{wr}}(G)$ is closed under unions. Hence, when nonempty, it has a unique maximal element $G^{\max}$, the *maximal weakly reversible realization graph*, which can be computed by solving a linear feasibility problem.

**Theorem.**

1. $\mathcal{K}_{\mathrm{disg}}(G) = \bigcup_{H \subseteq G^{\max}} \mathcal{K}_{\mathrm{disg}}(G,H) = \bigcup_{H \in \mathcal{H}_{\mathrm{wr}}(G)} \mathcal{K}_{\mathrm{disg}}(G,H)$, and the same holds for the flux cones.
2. If $\mathcal{F}_{\mathrm{disg}}(G) \ne \emptyset$, then $\mathcal{F}_{\mathrm{disg}}(G)$ is the positive part of the closure of $\mathcal{F}_{\mathrm{disg}}(G,G^{\max})$, and its relative interior is exactly $\mathcal{F}_{\mathrm{disg}}(G,G^{\max})$.
3. If moreover the kinetic subspace equals the stoichiometric subspace for all rate constants, the manifold interior of $\mathcal{K}_{\mathrm{disg}}(G)$ is $\mathcal{K}_{\mathrm{disg}}(G,G^{\max})$, and $\dim \mathcal{K}_{\mathrm{disg}}(G) = \dim \mathcal{K}_{\mathrm{disg}}(G,G^{\max})$. The faces $\sigma$ of the closed flux cone meeting the open orthant correspond to graphs $G^{\max}_\sigma$ with $\operatorname{relint}(\sigma) = \mathcal{F}_{\mathrm{disg}}(G,G^{\max}_\sigma)$, and the sets $\mathcal{K}_{\mathrm{disg}}(G,G^{\max}_\sigma)$ stratify $\mathcal{K}_{\mathrm{disg}}(G)$.

So a single weakly reversible graph, computable by linear programming, carries all generic disguised complex-balanced behavior of $G$; smaller realization graphs only contribute boundary strata.

## Depends on

- [Flux parametrization of the disguised toric locus](flux-parametrization-of-the-disguised-toric-locus.md)

## Expansion

Closure under unions: if $(G,\kappa_1)$ is realized on $H_1$ and $(G,\kappa_2)$ on $H_2$, then $(G,\kappa_1 + \kappa_2)$ is realized on $H_1 \cup H_2$ with the summed rate constants extended by zero. For fluxes, if $H_1 \subseteq H_2$ are both in $\mathcal{H}_{\mathrm{wr}}(G)$ then $\mathcal{F}_{\mathrm{disg}}(G,H_1) \subseteq \overline{\mathcal{F}_{\mathrm{disg}}(G,H_2)}$, because a vertex-balanced flux on $H_1$ plus a small vertex-balanced flux on $H_2$ realizes a nearby point of the larger set. Each $\mathcal{F}_{\mathrm{disg}}(G,H)$ is the relative interior of a projection of a polyhedral cone and lies in the relative interior of a single face, giving the face correspondence. The homeomorphism $\Psi(x,\beta) = (\beta_{y \to y'} x^{-y})$ transfers interior and strata from fluxes to rate constants.

## Sources

- Balázs Boros, Gheorghe Craciun, Oskar Henriksson, Jiaxin Jin, "A flux-based approach for analyzing the disguised toric locus of reaction networks", *Advances in Applied Mathematics* 182 (2027), 103160, Lemma 3.2, Definition 3.3, Theorem 3.4, Lemmas 4.7 and 4.8, Theorems 4.9 and 4.11, Corollary 5.4 (Theorem B), <https://doi.org/10.1016/j.aam.2026.103160> (preprint arXiv:2510.03621).
