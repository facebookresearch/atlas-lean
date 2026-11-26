# Dominant-eigenvalue signature of a critical transition

**Model.** Let $Z(t) = (z_1(t), \dots, z_n(t)) \in \mathbb{R}^n$ be the expression levels of $n$ molecules (genes or proteins) sampled at discrete times $t = 0, 1, 2, \dots$, evolving as

$$Z(t+1) = f\big(Z(t); P\big) + \text{noise},$$

near a stable equilibrium $\bar Z(P)$, where $P$ is a slowly varying parameter (the disease driver). Assume the Jacobian $\partial f/\partial Z$ at $\bar Z$ is diagonalizable with distinct real eigenvalues $\lambda_1(P), \dots, \lambda_n(P)$, all with $|\lambda_i| < 1$ (the normal state is stable), and that the eigenvalue of largest modulus, the *dominant eigenvalue* $\lambda_1$, satisfies $|\lambda_1(P)| \to 1$ as $P \to P_c$ (a codimension-one bifurcation, the critical transition).

Write $\Delta Y(t) = S^{-1}\big(Z(t) - \bar Z\big)$ for the eigen-coordinates, so that to first order

$$\Delta Y(t+1) = \Lambda(P)\,\Delta Y(t) + \zeta(t), \qquad \Lambda(P) = \operatorname{diag}\big(\lambda_1(P), \dots, \lambda_n(P)\big),$$

with $\zeta(t)$ zero-mean Gaussian noise with covariances $\kappa_{ij} = \operatorname{Cov}(\zeta_i, \zeta_j)$, independent over time.

**Statement (dominant group).** The *dominant group*, or *dynamic network biomarker* (DNB), is the set of molecules $i$ whose coordinates load on the dominant eigen-direction (row $i$ of $S$ has a nonzero first entry). As $P \to P_c$:

1. for $i$ in the dominant group, the stationary variance of $z_i$ diverges;
2. for $i, j$ both in the dominant group, $|\operatorname{corr}(z_i, z_j)| \to 1$;
3. for $i$ in the dominant group and $j$ outside it, $\operatorname{corr}(z_i, z_j) \to 0$;
4. molecules outside the dominant group keep bounded variance.

In the formulation of Liu et al. with binary *transition variables* $x_i(t) = \mathbf{1}\{|z_i(t) - z_i(t-1)| > d_i\}$ (a large change at node $i$ between consecutive samples), the dominant group satisfies, for any lag $T > 0$: in the normal state $x_i(t+T)$ is independent of $x_j(t)$ for all $i, j$; near the transition $x_i(t+T)$ and $x_j(t)$ are strongly correlated when $i$ and $j$ are both in the dominant group, and remain independent when neither is.

## Expansion

For the scalar autoregression $y_1(t+1) = \lambda_1 y_1(t) + \zeta_1(t)$ the stationary variance is $\kappa_{11}/(1 - \lambda_1^2)$ and the lag-one autocorrelation is $\lambda_1$, so both blow up or tend to one as $|\lambda_1| \to 1$ (critical slowing down). Every other eigen-coordinate keeps variance $\kappa_{ii}/(1 - \lambda_i^2)$, bounded because $|\lambda_i|$ stays away from $1$. Mapping back with $Z - \bar Z = S\,\Delta Y$, $z_i = \sum_k S_{ik}\, y_k$: if $S_{i1} \ne 0$ then $\operatorname{Var}(z_i) \approx S_{i1}^2 \operatorname{Var}(y_1)$ is dominated by the diverging mode, which gives (1); two such molecules become asymptotically proportional to the same $y_1$, which gives (2); a molecule with $S_{j1} = 0$ has bounded variance and its covariance with $z_i$ is bounded, so dividing by the diverging standard deviation of $z_i$ gives (3) and (4). The transition-variable form follows by applying the same reasoning to increments $Z(t) - Z(t-1)$ and thresholding.

## Sources

- R. Liu, M. Li, Z.-P. Liu, J. Wu, L. Chen, K. Aihara, "Identifying critical transitions and their leading biomolecular networks in complex diseases", *Scientific Reports* 2 (2012) 813. Results (dominant-group conditions in transition variables, proved as Theorem 2 of the Supplementary Information) and Methods, "Dynamical networks" (Eq. (6) and the diagonalized linearization, Eq. (8)). <https://doi.org/10.1038/srep00813>. PMCID: PMC3517980.
