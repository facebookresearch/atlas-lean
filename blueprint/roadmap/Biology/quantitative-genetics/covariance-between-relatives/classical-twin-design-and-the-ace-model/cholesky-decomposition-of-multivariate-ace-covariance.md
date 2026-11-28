# Cholesky decomposition of multivariate genetic and environmental covariance

**Model.** Extend the ACE decomposition to $p$ traits measured on the same individuals. Let $\Sigma_A$, $\Sigma_C$, $\Sigma_E$ be the $p \times p$ additive genetic, shared-environmental and nonshared-environmental covariance matrices, so that the phenotypic covariance is $\Sigma_P = \Sigma_A + \Sigma_C + \Sigma_E$, the cross-trait covariance between two members of a family is $\lambda \Sigma_A + \Sigma_C$ with $\lambda = 1$ for monozygotic and $\lambda = 1/2$ for dizygotic pairs, and each component is parameterized by its lower-triangular Cholesky factor,

$$\Sigma_A = L_A L_A^{\mathsf T}, \qquad \Sigma_C = L_C L_C^{\mathsf T}, \qquad \Sigma_E = L_E L_E^{\mathsf T}, \qquad (L_\bullet)_{kl} = 0 \text{ for } l > k .$$

**Properties.**
1. *Guaranteed admissibility and exact saturation.* Every lower-triangular $L$ gives a positive semidefinite $\Sigma = LL^{\mathsf T}$, and every positive semidefinite $\Sigma$ arises this way, so the triangular parameterization is an unconstrained and exactly saturated reparameterization of each component: it imposes no structure on the component covariances and no ordering assumption is being tested.
2. *Sequential interpretation.* With traits ordered $1, \dots, p$, the $k$-th latent factor of a component loads only on traits $k, \dots, p$. Hence the genetic variance of the last trait splits into the part explained by the latent genetic factors of the earlier traits, $\sum_{l<p} (L_A)_{pl}^2$, and the residual $(L_A)_{pp}^2$ specific to it. Placing a trait last therefore quantifies how much of its heritable variance is independent of the genes acting on the others.
3. *Genetic and environmental correlations.* The component correlations

$$r_A(k,l) = \frac{(\Sigma_A)_{kl}}{\sqrt{(\Sigma_A)_{kk}(\Sigma_A)_{ll}}}, \qquad r_E(k,l) = \frac{(\Sigma_E)_{kl}}{\sqrt{(\Sigma_E)_{kk}(\Sigma_E)_{ll}}}$$

decompose the phenotypic correlation as

$$r_P(k,l) = h_k h_l\, r_A(k,l) + c_k c_l\, r_C(k,l) + e_k e_l\, r_E(k,l),$$

with $h^2$, $c^2$, $e^2$ the component proportions of each trait's variance. Because the three terms can carry opposite signs, a phenotypic correlation near zero is consistent with substantial genetic correlation offset by environmental correlation of the other sign; the multivariate fit, not the phenotypic correlation, decides.

**Model choice.** Dropping a whole component (setting $L_C = 0$, the multivariate AE model) is a nested hypothesis with $p(p+1)/2$ constraints, tested by a likelihood-ratio chi-square against the full model.

## Depends on

- [The ACE variance-component model for twin and sibling data](ace-variance-component-model-for-twins.md)

## Expansion

Statement 1 is the existence and uniqueness of the Cholesky factorization for positive definite matrices, with the semidefinite boundary obtained as a limit; its value in fitting is that the optimizer may roam over all of $\mathbb R^{p(p+1)/2}$ without producing an inadmissible covariance, which an unconstrained parameterization of $\Sigma$ by its entries would not. Statement 2 restates the triangular pattern: trait $k$ loads on factors $1, \dots, k$ only. The ordering changes the factors but not the fitted $\Sigma$ or its fit, so the decomposition is descriptive rather than causal, and a claim read from one ordering must be stable under reordering unless the ordering is justified outside the data. Statement 3 follows by writing each phenotypic covariance as the sum of the three component covariances and dividing by the phenotypic standard deviations. A test for the absence of a genetic overlap is a test of $r_A(k,l) = 0$, which in small twin samples has low power, so a near-zero estimated genetic correlation bounds rather than excludes a shared genetic basis.

## Sources

- L. Rietschel, F. Streit, G. Zhu, K. McAloney, J. Frank, B. Couvy-Duchesne, S. H. Witt, T. M. Binz, et al., *Hair cortisol in twins: heritability and genetic overlap with psychological variables and stress-system genes*, Scientific Reports 7 (2017), 15351, <https://doi.org/10.1038/s41598-017-11852-3>, PMCID PMC5703444. Methods, "Twin correlations, heritability of HCC, and shared covariance with psychological variables" (simultaneous Cholesky decomposition of the additive genetic, shared and unique environmental covariance in the absence of a clear factor structure, non-proportional loadings across the three sources, trait ordering chosen so that the last trait's genetic variance splits into the part shared with the earlier traits and the part independent of them, comparison of ACE with AE and CE Cholesky models) and Results, "Correlation of HCC with psychological variables" (the shared-environment component dropped without worsening fit, genetic correlations reported from the AE model, and the possibility of opposite-signed genetic and environmental correlations cancelling in the phenotypic correlation). The algebraic properties are standard and derived here.
