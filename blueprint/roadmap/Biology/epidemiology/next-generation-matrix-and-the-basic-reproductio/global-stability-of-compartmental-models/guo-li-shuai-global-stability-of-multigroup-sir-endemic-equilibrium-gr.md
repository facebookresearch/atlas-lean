# Global stability of the endemic equilibrium of multigroup SIR models

Guo, Li and Shuai (2006) study the $n$-group SIR model with immunization, whose reduced system (1.3) is

$$\dot S_k = (1 - p_k)\Lambda_k - (d^S_k + \theta_k)S_k - \sum_{j=1}^n \beta_{kj}S_k I_j, \qquad \dot I_k = \sum_{j=1}^n \beta_{kj}S_k I_j - (d^I_k + \epsilon_k + \gamma_k)I_k,$$

on its compact positively invariant region $\Gamma$, with $R_0 = \rho(M_0)$ the spectral radius of the matrix $M_0$ of Eq. (1.6). For irreducible $B = (\beta_{kj})$ they prove: if $R_0 \le 1$, the disease-free equilibrium is the unique equilibrium and is globally stable in $\Gamma$, and if $R_0 > 1$ it is unstable and the system is uniformly persistent in the interior of $\Gamma$ (Proposition 3.1); if $R_0 > 1$, there is a unique endemic equilibrium, which is globally asymptotically stable in the interior of $\Gamma$ (Theorem 3.3). The Lyapunov function for Theorem 3.3 is a weighted sum of Volterra-type functions of the groups, with weights given by the diagonal cofactors of the Laplacian of the weighted digraph with arc weights $\beta_{kj}S_k^* I_j^*$; Lemma 2.1 of the source expresses these cofactors as sums over directed trees rooted at each vertex (Kirchhoff's matrix-tree theorem).

## Proof depends on

- [LaSalle's invariance principle](../../../../Dynamics/smooth-dynamics/lasalle-s-invariance-principle/lasalle.md)

## Expansion

1. The model (1.2)–(1.3), the invariant region $\Gamma$, the matrix $M_0$ and $R_0$.
2. Proposition 3.1: the disease-free case and uniform persistence for $R_0 > 1$.
3. Existence and uniqueness of the endemic equilibrium for $R_0 > 1$.
4. Lemma 2.1 (directed trees, cofactors and the kernel of the Laplacian) and the cycle identity used to sign the Lyapunov derivative.
5. Theorem 3.3 via [LaSalle's invariance principle](../../../../Dynamics/smooth-dynamics/lasalle-s-invariance-principle/lasalle.md).

## Sources

- H. Guo, M. Y. Li and Z. Shuai, Global stability of the endemic equilibrium of multigroup SIR epidemic models, Can. Appl. Math. Q. 14 (2006), 259–284, Lemma 2.1, Proposition 3.1 and Theorem 3.3.
