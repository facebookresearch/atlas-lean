# The Kolmogorov backward equation for Wright–Fisher diffusions

For a one-dimensional diffusion with drift $\mu$ and infinitesimal variance $\sigma^2$ and a bounded test function $f$, the Chapman–Kolmogorov equation gives that $u(t, x) = E_x[f(X_t)]$ satisfies the backward equation $\partial_tu = \mu u' + \frac12\sigma^2u''$ with $u(0, \cdot) = f$, and that the transition density satisfies the same equation in its initial point, with a point mass at $x$ as initial condition (Karlin and Taylor 1981, Chapter 15). For the Wright–Fisher diffusion with selection and mutation this reads

$$\partial_tu(t, x) = \tfrac12x(1 - x)\,\partial_x^2u(t, x) + \bigl(\sigma x(1 - x) + \tfrac12(\theta_1(1 - x) - \theta_2x)\bigr)\partial_xu(t, x).$$

In the neutral case without mutation the identity holds in the strong semigroup sense on polynomials: $s \mapsto T_sp$ is differentiable in the sup norm with derivative $T_t(\frac12X(1 - X)p'')$. For the generalized Kimura operators of Epstein and Pop (2019), which include multi-dimensional Wright–Fisher generators on compact manifolds with corners, the martingale problem is well posed (Theorem 1.3) and the Dirichlet heat kernel of Theorem 1.7 is a weak solution of the backward Kolmogorov equation in its initial point and of the forward equation in its final point (Section 3). The statement here is the backward equation for $u = E_x[f(X_t)]$ with the regularity of $u$ named in each use: the sup-norm semigroup identity on the generator's domain, the classical $C^{1,2}$ equation in the interior, and the weak equation of the heat kernel.

## Depends on

- [Polynomial semigroup dynamics](../../../../Biology/population-genetics/diffusion-theory/wright-fisher-semigroup-and-moment-duality/has-deriv-at-wf-semigroup-to-continuous.md)
- [Generator of the Wright–Fisher diffusion with selection and mutation](../../../../Biology/population-genetics/diffusion-theory/wright-fisher-diffusion-with-selection-and-mutat/selection-mutation-generator.md)
- [Martingale problems](../../../../Probability/markov-chains/martingale-problems/martingale-problems-generic-definition.md)

## Expansion

1. The backward equation from the Chapman–Kolmogorov equation and the generator, as in Karlin and Taylor (1981, Chapter 15).
2. The sup-norm identity $\frac{d}{dt}T_tf = LT_tf = T_tLf$ for $f$ in the domain of the generator, extending the polynomial case.
3. The classical interior equation for $u$ with continuous initial data, from interior smoothness of the transition density.
4. The weak backward equation of the Dirichlet heat kernel for generalized Kimura operators, and the behaviour of $u$ at the boundary.

## Sources

- S. Karlin and H. M. Taylor, *A Second Course in Stochastic Processes*, Academic Press, 1981, Chapter 15.
- C. L. Epstein and C. A. Pop, Transition probabilities for degenerate diffusions arising in population genetics, Probab. Theory Related Fields 173 (2019), 537–603; Theorems 1.3 and 1.7 and Section 3 in the numbering of the arXiv version, arXiv:1608.02119v2. <https://doi.org/10.1007/s00440-018-0840-2>
