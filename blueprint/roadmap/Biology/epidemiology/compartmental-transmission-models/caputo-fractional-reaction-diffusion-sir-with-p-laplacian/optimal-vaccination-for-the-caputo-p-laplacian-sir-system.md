# Optimal vaccination for the Caputo time-fractional SIR system with $p$-Laplacian diffusion

For the [Caputo time-fractional reaction–diffusion SIR system](well-posedness-of-the-caputo-p-laplacian-sir-system.md) on $\Omega_{\mathcal{T}} = \Omega \times [0,\mathcal{T}]$ with vaccination control $u$ moving susceptibles to the recovered class, consider the objective

$$
\mathcal{J}(S,I,R,u) = \|I(\cdot,\mathcal{T})\|_{L^2(\Omega)}^2 + \|I\|_{L^2(\Omega_{\mathcal{T}})}^2 + \eta\, \|u\|_{L^2(\Omega_{\mathcal{T}})}^2, \qquad \eta > 0,
$$

over the admissible set $U_{ad} = \{ v \in L^\infty(\Omega_{\mathcal{T}}) : 0 < v,\ \|v\|_{L^\infty} < 1 \}$.

**Theorem.**

1. (Existence) There is an optimal pair $(\nu^*, u^*)$ with $\nu^* = (S^*, I^*, R^*) \in (L^\infty(\Omega_{\mathcal{T}}))^3$ minimizing $\mathcal{J}$.
2. (Necessary condition) If $u^*$ is optimal and $\rho = (\rho_1,\rho_2,\rho_3)$ solves the adjoint system, a backward problem driven by the backward Caputo derivative ${}^{C}_{\mathcal{T}}D^{\alpha}_t$, then

$$
u^* = \min\Big\{ 1,\ \max\Big( 0,\ -\frac{S^*}{\eta} (\rho_1 - \rho_3) \Big) \Big\}.
$$

## Depends on

- [Well-posedness of the Caputo time-fractional SIR system with p-Laplacian diffusion](well-posedness-of-the-caputo-p-laplacian-sir-system.md)

## Expansion

A minimizing sequence of controls is bounded in $L^\infty$, so it has a weak-* limit. The states are bounded uniformly, and a time-derivative estimate involving the Mittag-Leffler function $E_\alpha(-\gamma \mathcal{T}^\alpha)$ yields enough compactness to pass to the limit in the bilinear term $\mu S I$. Lower semicontinuity of $\mathcal{J}$ then gives an optimal pair. For the characterization, the Gâteaux derivative of the control-to-state map is computed, and the fractional integration-by-parts formula moves ${}^{C}D^{\alpha}_t$ onto the adjoint as the backward Caputo derivative. The variational inequality for the convex control set then reduces pointwise to the projection formula above.

## Sources

- Achraf Zinihi, Moulay Rchid Sidi Ammi, Delfim F. M. Torres, "Fractional differential equations of a reaction-diffusion SIR model involving the Caputo-fractional time-derivative and a nonlinear diffusion operator", Evolution Equations and Control Theory 14 (2025), 944–967, <https://doi.org/10.3934/eect.2025018>. Published version of arXiv:2502.00509, cited next; locators there refer to the arXiv version.
- Achraf Zinihi, Moulay Rchid Sidi Ammi, Delfim F. M. Torres, "Fractional differential equations of a reaction-diffusion SIR model involving the Caputo-fractional time-derivative and a nonlinear diffusion operator", arXiv (2025). Lemma 4.2, Lemma 5.1, Theorem 5.2, Theorem 6.1. <https://doi.org/10.48550/arXiv.2502.00509>
