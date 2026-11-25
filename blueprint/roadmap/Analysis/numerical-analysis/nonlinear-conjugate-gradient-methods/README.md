# Nonlinear conjugate gradient methods

Nonlinear conjugate gradient methods extend the linear conjugate gradient method to smooth unconstrained minimisation: $d_0 = -g_0$ and $d_{k+1} = -g_{k+1} + \beta_k d_k$, where $g_k = \nabla f(x_k)$ and the scalar $\beta_k$ is chosen so that the method reduces to linear conjugate gradients on a strictly convex quadratic with exact line searches. The Fletcher–Reeves, Polak–Ribière–Polyak and Hestenes–Stiefel choices are analysed under the strong Wolfe conditions; the Dai–Yuan choice $\beta_k = \|g_{k+1}\|^2 / d_k^\top (g_{k+1} - g_k)$ converges globally under the standard Wolfe conditions.

- [Dai–Yuan conjugate gradient parameter](dai-yuan-beta.md)
- [The Dai–Yuan identity](inner-dai-yuan-direction.md)
- [Descent of the Dai–Yuan direction](inner-dai-yuan-direction-neg.md)
- [Global convergence of the Dai–Yuan method](dai-yuan-liminf-norm-gradient.md)
- [Global convergence of the Fletcher–Reeves method under strong Wolfe steps](fletcher-reeves-liminf-norm-gradient.md)

## Related topics

- [Conjugate gradient method](../../../LinearAlgebra/matrix-decompositions/conjugate-gradient-method/README.md): the linear method for symmetric positive definite systems,
  to which these methods reduce on strictly convex quadratics with exact line searches.
- [Line search methods](../line-search-methods/README.md): the Wolfe conditions and the Zoutendijk
  condition used in every convergence proof here.
