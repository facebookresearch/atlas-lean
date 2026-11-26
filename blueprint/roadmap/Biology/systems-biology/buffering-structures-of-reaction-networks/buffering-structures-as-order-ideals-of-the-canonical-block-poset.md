# Buffering structures as order ideals of the canonical block poset

**Setting.** A reaction network $\mathcal N=(\mathbf M,\mathbf E)$ with species $\mathbf M$, reactions $\mathbf E$ and stoichiometric matrix $S$ has dynamics $\dot x=S\,r(x)$, where each rate $r_\rho$ depends on exactly its input species. The symbolic reactivity matrix $R\in\mathbb R(r_{\rho m})^{|\mathbf E|\times|\mathbf M|}$ has an independent indeterminate $r_{\rho m}$ where $X_m$ is an input of $\rho$ and $0$ elsewhere; assume the nondegeneracy condition $\det(SR)\not\equiv0$ (conservation laws absorbed). Let $C$ be a Gale dual of $S$, so $[\,R\mid C\,]$ is a square LM-matrix.

A subnetwork $\gamma=(\mathbf M',\mathbf E')$ is output-complete if every reaction with an input species in $\mathbf M'$ lies in $\mathbf E'$. Its influence index is
$$\lambda(\gamma)=|\mathbf E'|-|\mathbf M'|-\kappa(\mathbf E'),\qquad \kappa(\mathbf E')=|\mathbf E'|-\operatorname{rank}S[\mathbf M,\mathbf E'],$$
and $\gamma$ is a buffering structure if it is output-complete with $\lambda(\gamma)=0$. By the law of localization, perturbing a reaction inside a buffering structure changes steady-state concentrations and fluxes only inside it.

**Theorem.** Under nondegeneracy, $\lambda(\gamma)\ge0$ for every output-complete $\gamma$. Let $\mathcal P$ be the poset of CCF blocks of $[\,R\mid C\,]$, each block carrying a species set $\mathbf M_a$ and reaction set $M_a$. Then
$$J\ \longmapsto\ \gamma_J=\Big(\bigcup_{M_a\in J}\mathbf M_a,\ \bigcup_{M_a\in J}M_a\Big)$$
is an isomorphism from the lattice of order ideals of $(\mathcal P,\preceq)$ onto the buffering structures ordered by inclusion. Hence buffering structures form a distributive lattice closed under union and intersection, and the species set of a buffering structure is determined by its reactions.

**Corollaries.** (i) $\det(SR)$ is reducible in $\mathbb R[r_{\rho m}]$ iff $\mathcal N$ has a buffering structure with $\emptyset\ne\mathbf M'\subsetneq\mathbf M$. (ii) Let the influence graph be the CCF directed graph with edges reversed. Perturbing reaction $\rho$ changes the steady-state concentration of $X_m$ iff the influence graph has a directed path from the block containing $\rho$ to the block containing $X_m$.

## Depends on

- [Zero pattern of the inverse of a layered mixed matrix](zero-pattern-of-the-inverse-of-a-layered-mixed-matrix.md)

## Expansion

At a steady state the response of concentrations to a rate perturbation is given by blocks of $[\,R\mid C\,]^{-1}$ (implicit differentiation of $S\,r(x,k)=0$ together with the conservation laws), so influence is exactly the nonzero pattern of that inverse, which the CCF inverse theorem reads off. A buffering structure corresponds to a down-closed set of blocks: output-completeness and $\lambda=0$ say that $[\,R\mid C\,]$ is block upper-triangular with the subnetwork as a block, and the finest such triangularization is the CCF. The determinant factors are the determinants of the diagonal CCF blocks, which gives (i).

## Sources

- A. Kuhrs, M. L. Telek, N. Vassena, "Layered mixed matrices and reaction networks", arXiv:2609.05100 (2026), Section 3 (Definition of $\lambda$, Theorem 3.12, Theorem 3.17, Corollary 3.19, Proposition 3.21, Theorem 3.23), <https://doi.org/10.48550/arXiv.2609.05100>.
