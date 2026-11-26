# Child-selection matrices and bifurcations in parameter-rich reaction networks

**Setting.** A reaction network on species $M$ and reactions $E$ has stoichiometric matrix $S = S^+ - S^-$ (product and reactant coefficients) and monotone reaction rates $\mathbf r(x, p)$, so $\dot x = S\mathbf r(x,p)$ with Jacobian $G = S R$, $R = \partial \mathbf r/\partial x$ the reactivity matrix ($R_{jm} > 0$ iff $S^-_{mj} > 0$). Kinetics are *parameter-rich* if at every positive steady state every symbolic reactivity matrix is realised by some parameter choice (as for Michaelis–Menten, Hill and generalised mass-action kinetics). A *$k$-child-selection* is a triple $\boldsymbol\kappa = (\kappa, E_\kappa, J)$ with $\kappa \subseteq M$, $E_\kappa \subseteq E$, $|\kappa| = |E_\kappa| = k$, and a bijection $J : \kappa \to E_\kappa$ such that each species $X_m$ is a reactant of $J(X_m)$; its *CS-matrix* is $S[\boldsymbol\kappa]_{ml} = s^+_{mJ(l)} - s^-_{mJ(l)}$. $S[\boldsymbol\kappa]$ is an *unstable-positive feedback* if $\operatorname{sign}\det S[\boldsymbol\kappa] = (-1)^{k-1}$ and no smaller principal submatrix has this property; an *unstable-negative feedback* if it is Hurwitz-unstable with $\operatorname{sign}\det S[\boldsymbol\kappa] = (-1)^k$ and no smaller principal submatrix is Hurwitz-unstable.

**Theorem.** Let the network be consistent and nondegenerate (an invertible CS-matrix of size $|M| - n$ exists, $n$ the number of conservation laws), with parameter-rich kinetics.
1. If some $(|M|-n)$-CS-matrix is Hurwitz-stable, the network admits a stable positive steady state; if some CS-matrix is Hurwitz-unstable, it admits an unstable one.
2. The network is autocatalytic iff some CS-matrix is an unstable-positive feedback that is a Metzler matrix.
3. The network admits multistationarity iff there are two $(|M|-n)$-CS-matrices with $\det S[\boldsymbol\kappa_1]\,\det S[\boldsymbol\kappa_2] < 0$.
4. If a Hurwitz-stable CS-matrix has a strict principal submatrix that is an unstable-positive feedback, or an unstable-negative feedback has a Hurwitz-stable principal submatrix of one size less, then for some parameters the system has nonstationary periodic solutions.

## Expansion

By the Cauchy–Binet formula, each coefficient of the characteristic polynomial of $G = SR$ is a sum over child-selections of $\det S[\boldsymbol\kappa]$ times a product of reactivities. Parameter richness lets one make the reactivities of a single child-selection dominate, so the Jacobian approaches $S[\boldsymbol\kappa]$ times a positive diagonal matrix on the selected species. Spectral properties of CS-matrices are then realised by actual Jacobians, sign changes of the determinant across selections produce zero-eigenvalue (fold) bifurcations, and nested stable/unstable selections give Hopf bifurcations. The BiRNe module enumerates minimal autocatalytic subnetworks and these sign conditions symbolically for networks with 10–20 species.

## Sources

- R. Golnik, T. Gatter, P. F. Stadler, N. Vassena, "BiRNe: Symbolic bifurcation analysis of reaction networks with Python", arXiv:2511.14431 (2025), Proposition 2.2 and the Child-Selection definitions, Propositions 2.7, 2.10 and 2.11, Theorems 2.15, 2.16, 2.17 and 2.18, <https://doi.org/10.48550/arXiv.2511.14431>.
