# Hessian Cramér–Rao bound and absolute sensitivity of reaction networks

**Setting.** A chemical reaction network on $n$ species has stoichiometric matrix $S$; let $U$ be a $q\times n$ matrix whose rows form a basis of $\operatorname{Ker}[S^{*}]$ (conservation laws), $q=\dim\operatorname{Ker}[S^{*}]$, so $\eta = Ux$ is the vector of conserved quantities. The concentration space $X\subset\mathbb{R}^n_{>0}$ carries a strictly convex free-energy function $\phi$ (for an ideal, quasi-thermostatic network $\phi(x)=\sum_i x^i(\log x^i - 1 - \log x_0^i)$ up to affine terms), whose Hessian defines the Riemannian metric $g_X = \sum_{i,j}\partial_i\partial_j\phi\,dx^i\otimes dx^j$. The equilibrium manifold $\mathcal{V}$ through a base point is mapped bijectively onto the space $H=U(X)$ of conserved-quantity vectors by $U$, with inverse $\beta:H\to\mathcal{V}$.

**Theorem (Hessian Cramér–Rao bound).** At every $x$,

$$g_X \succeq U^{*}\, g_H\, U, \qquad g_H = \big[\,U g_X^{-1} U^{*}\big]^{-1},$$

i.e. the difference is positive semidefinite, and $[U^{*}g_HU]_{ij} = \langle \pi(\partial_i), \pi(\partial_j)\rangle_{g_X}$ where $\pi:T_xX\to T_x\mathcal{V}$ is the $g_X$-orthogonal projection.

**Theorem (absolute sensitivity).** The matrix of absolute sensitivities $A(x) = D_{Ux}\beta\; D_xU$, whose entry $A(x)^i_j = \sum_{k}\frac{\partial x^i}{\partial\eta^k}u^k_j$ measures how a perturbation of the concentration of species $j$ redistributes to species $i$ after re-equilibration, represents the $g_X$-orthogonal projection $\pi: T_xX\to T_x\mathcal{V}$, with $A(x)^i_j = \langle dx^i, \pi(\partial_j)\rangle$. Consequently $A(x)$ does not depend on the choice of basis of $\operatorname{Ker}[S^{*}]$, and its trace equals the number of independent conservation laws:

$$\operatorname{Tr}A(x) = \sum_{i=1}^n A(x)^i_i = q .$$

## Expansion

Legendre duality between concentrations and chemical potentials and the parameterisation of $\mathcal{V}$ by conserved quantities are isometries for the Hessian metrics, so $g_H$ is the metric induced on $\mathcal{V}$; the bound expresses that restricting a quadratic form to a subspace and pulling it back by the projection can only decrease it. A projection onto a $q$-dimensional subspace has trace $q$, which gives the sum rule for the diagonal absolute sensitivities.

## Sources

- D. Loutchko, Y. Sughiyama, T. J. Kobayashi, "Information geometry of chemical reaction networks: Cramer-Rao bound and absolute sensitivity revisited", arXiv:2503.19384, Theorem 4.2, Corollary 4.1 and Section 5 (absolute sensitivity, Theorem 5.1 and the projection theorem). <https://doi.org/10.48550/arXiv.2503.19384>
