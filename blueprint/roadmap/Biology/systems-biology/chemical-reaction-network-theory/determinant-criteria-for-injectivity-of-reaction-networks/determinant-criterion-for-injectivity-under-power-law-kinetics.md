# Determinant criterion for injectivity of reaction networks under power-law kinetics

**Setting.** A network of interacting species with $n$ species and $m$ reactions has stoichiometric matrix $A \in \mathbb{R}^{n\times m}$ of rank $s$; concentrations evolve by $\dot{c} = AK(c)$, $c \in \mathbb{R}^n_{>0}$, so trajectories stay in stoichiometric classes $c_0 + \operatorname{im}(A)$. A power-law kinetics is

$$K_j(c) = k_j\,c^{v_j} = k_j\prod_{i=1}^n c_i^{v_{j,i}},\qquad k_j > 0,\ v_j \in \mathbb{R}^n,$$

specified by the rate vector $\kappa = (k_1,\dots,k_m)$ and the kinetic order matrix $V \in \mathbb{R}^{m\times n}$ with rows $v_j$; mass-action kinetics and S-systems are special cases. $A$ is injective over a class of kinetics if $AK(a) \ne AK(b)$ for all distinct stoichiometrically compatible $a, b \in \mathbb{R}^n_{>0}$ and every kinetics $K$ in the class. Injectivity precludes multiple positive steady states in any stoichiometric class.

**Extended rate function.** Reorder species so that $\operatorname{im}(A)^\perp$ ($d = n - s$) has a reduced basis $\omega^1,\dots,\omega^d$ with $\omega^i_i = 1$ and $\omega^i_j = 0$ for $j \le d$, $j \ne i$. Define

$$\tilde{f}_K(c) = \big(\omega^1\cdot c,\dots,\omega^d\cdot c,\ (AK(c))_{d+1},\dots,(AK(c))_n\big).$$

A steady state $c$ is degenerate iff $\ker J_c(AK) \cap \operatorname{im}(A) \ne \{0\}$, iff $\det J_c(\tilde{f}_K) = 0$.

**Theorem (Jacobian criterion).** For fixed kinetic order $V$, the following are equivalent:
1. $A$ is injective over all power-law kinetics $(\kappa, V)$ with $\kappa \in \mathbb{R}^m_{>0}$;
2. $\det J_c(\tilde{f}_{\kappa,V}) \ne 0$ for all $c \in \mathbb{R}^n_{>0}$ and $\kappa \in \mathbb{R}^m_{>0}$.

**Expansion of the determinant.** $\det J_c(\tilde{f}_{\kappa,V})$ is homogeneous of degree $s$ in $\kappa$ and linear in each $k_j$; the coefficient of $\prod_{j\in J}k_j$ ($|J| = s$) is

$$c^{-\mathbf{1} + \sum_{j\in J}v_j}\sum_{|I| = s}\det(A_{I,J})\det(V_{J,I})\prod_{i\notin I}c_i.$$

**Theorem (minor criterion).** $A$ is injective over all power-law kinetics with kinetic order $V$ iff the nonzero products $\det(A_{I,J})\det(V_{J,I})$, over index sets $I \subseteq \{1,\dots,n\}$, $J \subseteq \{1,\dots,m\}$ with $|I| = |J| = s$, all have the same sign, and at least one of them is nonzero.

## Expansion

The Jacobian of the power-law rate function factors as $J_c(AK) = A\,\operatorname{diag}(K(c))\,V\,\operatorname{diag}(c)^{-1}$. A matrix-theoretic lemma shows $\det(\tilde{M}) = \sum_{|I|=s}\det(M_{I,I})$ when the columns of $M$ lie in an $s$-dimensional space, and Cauchy–Binet turns each principal minor into $\sum_J \det(A_{I,J})\det(V_{J,I})\prod_{j\in J}K_j$. If all nonzero products share a sign the determinant never vanishes. The equivalence of a nonvanishing Jacobian determinant with injectivity extends the corresponding argument for mass-action kinetics: two distinct compatible points with equal rates can be converted into a positive point and rate vector at which the Jacobian has a nontrivial kernel vector in $\operatorname{im}(A)$, and conversely. Terms of opposite sign let one choose $\kappa$ and $c$ making the determinant vanish. The criterion is purely combinatorial in $A$ and $V$ and is easy to check symbolically.

## Sources

- Carsten Wiuf and Elisenda Feliu, "Power-Law Kinetics and Determinant Criteria for the Preclusion of Multistationarity in Networks of Interacting Species", SIAM Journal on Applied Dynamical Systems 12 (2013), 1685–1721, <https://doi.org/10.1137/120873388>; numbering as in arXiv:1202.3621: Section 5 (Propositions 5.2 and 5.3), Section 6 (Definitions 6.1, 6.3 and 6.5), Theorem 8.1 and Propositions 8.2 and 8.4.
