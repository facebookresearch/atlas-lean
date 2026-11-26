# Sorting and engulfment regimes of two-species adhesion surface tensions

**Setting.** Two cell types ($N = 2$) evolve by the multispecies Patlak–Keller–Segel system with interaction matrix $A = \begin{pmatrix}\alpha_{11} & \alpha_{12}\\ \alpha_{12} & \alpha_{22}\end{pmatrix}$, positive semidefinite with no repeated or zero column (equivalently $\alpha_{11},\alpha_{22} > 0$ and $\alpha_{12}^2 \le \alpha_{11}\alpha_{22}$, $A$ having distinct columns), and the vacuum condition holds. Let $\sigma_{01}, \sigma_{02}, \sigma_{12}$ be the surface tensions (vacuum/species 1, vacuum/species 2, species 1/species 2) of the Γ-limit interfacial energy, defined as geodesic distances between the wells $0$, $\theta_1 e_1$, $\theta_2 e_2$.

**Theorem.**
1. *(Complete sorting.)* If $\alpha_{12} = 0$, then $\sigma_{12} = \sigma_{01} + \sigma_{02}$: an interface between the two types costs as much as two free surfaces, so the types separate completely.
2. *(Partial engulfment.)* There is $\gamma_0 = \gamma_0(\alpha_{11},\alpha_{22},m,\sigma) > 0$ such that for $0 < \alpha_{12} < \gamma_0$ all triangle inequalities are strict: $\sigma_{ij} < \sigma_{ik} + \sigma_{kj}$ for every permutation $(i,j,k)$ of $(0,1,2)$, so triple junctions with nondegenerate contact angles occur.
3. *(Full engulfment.)* If $\alpha_{11} > \alpha_{22} > 0$ and $\alpha_{12} \ge \alpha_{22}$, then $\sigma_{01} = \sigma_{02} + \sigma_{21}$: the more cohesive type 1 never touches the vacuum and is enveloped by type 2.

These are the mixing-free regimes predicted by the Differential Adhesion Hypothesis; numerically the transition from partial to full engulfment occurs at a critical cross-adhesion $\gamma_c \in [\gamma_0, \min\{\alpha_{11},\alpha_{22}\}]$.

## Depends on

- [Γ-convergence of the multispecies Keller–Segel energy to an interfacial energy](gamma-convergence-of-the-multispecies-keller-segel-energy-to-an-interfacial-energy.md)

## Expansion

Equality $\sigma_{ij} = \sigma_{ik} + \sigma_{kj}$ means a minimizing (almost-)geodesic from well $i$ to well $j$ passes through well $k$. For a diagonal matrix $A$ (any $N$), superadditivity of $f_m$, $\sum_j f_m(\rho_j) \le f_m(\sum_j \rho_j)$, gives a lower bound of the weight by a sum of one-dimensional weights, and Cauchy–Schwarz shows the geodesic between two species wells is the broken line through the origin; hence $\sigma_{ij} = \sigma_{i0} + \sigma_{0j}$ and the limit energy is $2\sum_i \sigma_{0i}\mathcal{H}^{d-1}(\partial^*E_i \cap \Omega)$. Parts 2 and 3 follow from a phase-plane analysis of the geodesics for $N = 2$, and numerical simulations locate the transition between them.

## Sources

- J. Jang and A. Mellet, "Cell-cell adhesion and multiphase Hele–Shaw problem as the singular limit of a Keller–Segel system", arXiv:2606.10205 (2026), Theorem 1.2, Section 5 (Proposition 5.1 for diagonal interaction matrices) and Appendix B (numerics on the engulfment transition), <https://doi.org/10.48550/arXiv.2606.10205>.
