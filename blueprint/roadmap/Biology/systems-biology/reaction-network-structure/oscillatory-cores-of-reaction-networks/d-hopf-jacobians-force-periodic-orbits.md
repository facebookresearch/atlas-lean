# D-Hopf Jacobians force periodic orbits

**Setting.** A reaction network with species set $M$, reactions $E$ and stoichiometric matrix $\mathbb S\in\mathbb R^{|M|\times|E|}$ evolves by $\dot{\mathbf x}=\mathbb S\,\mathbf r(\mathbf x)$. Its symbolic Jacobian is $G=\mathbb S R$, where the reactivity matrix $R_{jm}=\partial r_j/\partial x_m$ is nonzero exactly when species $m$ is a reactant of reaction $j$. Kinetics are *parameter-rich* when, at any positive steady state, the steady-state fluxes and the nonzero reactivities can be prescribed independently by choosing parameters (Michaelis–Menten and Hill kinetics qualify). The network is *nondegenerate* if its dynamics have dimension $|M|-n$, where $n=\dim\ker\mathbb S^T$ is the number of independent linear conservation laws.

**Definition (D-Hopf matrix).** An $n\times n$ matrix $A$ is D-Hopf if some invertible $k\times k$ principal submatrix $A[\kappa]$ and two positive diagonal matrices $D_1,D_2$ satisfy $\operatorname{inertia}(A[\kappa]D_1)\ne\operatorname{inertia}(A[\kappa]D_2)$.

**Child-Selection matrices.** A CS triple $\boldsymbol\kappa=(\kappa,E_\kappa,J)$ pairs each species $m\in\kappa$ bijectively with a reaction $J(m)\in E_\kappa$ in which $m$ is a reactant; the CS-matrix is $\mathbb S[\boldsymbol\kappa]_{mn}=\mathbb S_{mJ(n)}$. Without explicit catalysis these are square submatrices of $\mathbb S$ with negative diagonal after column permutation.

**Lemma 2.3.** If $A$ is D-Hopf, there is a positive diagonal $D$ such that $AD$ has purely imaginary eigenvalues.

**Theorem 2.4.** For a nondegenerate network, if for some parameter choice the Jacobian $G(\bar{\mathbf x})=\mathbb S R(\bar{\mathbf x})$ at a positive steady state is D-Hopf, then the system admits nonstationary periodic orbits.

**Corollary 2.8.** For a network with parameter-rich kinetics, if some CS-matrix $\mathbb S[\boldsymbol\kappa]$ is D-Hopf, the system admits periodic solutions.

## Expansion

Lemma 2.3: along the path $D(\mu)=(1-\mu)D_1+\mu D_2$ the matrix $A[\kappa]D(\mu)$ stays invertible (it is a product of an invertible matrix and a positive diagonal one), so its inertia can change only through eigenvalues crossing the imaginary axis away from zero; extending $D$ by small entries off $\kappa$ transfers this to $AD$. Theorem 2.4 is Fiedler's global Hopf bifurcation theorem (Theorem 7.3): along an analytic parameter path on which the Jacobian restricted to the stoichiometric class stays invertible but changes inertia, a global continuum of periodic orbits emanates (Lemma 7.4). Corollary 2.8 follows because, by Cauchy–Binet, shrinking every reactivity outside the CS pairing makes the principal submatrix $G[\kappa]$ approach $\mathbb S[\boldsymbol\kappa]\operatorname{diag}(R_{mJ(m)})$, and the paired reactivities act as the free positive diagonal.

## Sources

- A. Blokhuis, P. F. Stadler, N. Vassena, "Stoichiometric recipes for periodic oscillations in reaction networks", *Proceedings of the Royal Society A Mathematical Physical and Engineering Science* 482(2340) (2026), 20250886, Definition of D-Hopf matrices, Lemma 2.3, Theorem 2.4, Corollary 2.8, Theorem 7.3 and Lemma 7.4, <https://doi.org/10.1098/rspa.2025.0886> (preprint arXiv:2508.15273).
