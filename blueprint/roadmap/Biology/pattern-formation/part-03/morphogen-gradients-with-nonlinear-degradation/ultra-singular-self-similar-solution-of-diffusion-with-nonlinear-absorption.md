# Ultra-singular self-similar solution of diffusion with nonlinear absorption

**Setting.** A morphogen produced at the boundary $x = 0$ of a one-dimensional tissue, diffusing and undergoing nonlinear self-enhanced degradation of order $p > 1$, is modeled by $u_t = u_{xx} - u^p$ on $x > 0$. In the limit of an infinitely strong source with zero initial data,

$$u_t = u_{xx} - u^p \ \ (x,t) \in (0,\infty)^2, \qquad u(0,t) = \infty, \qquad u(x,0) = 0,$$

which has the singular stationary solution

$$v_\infty(x) = \Big(\frac{2(p+1)}{(p-1)^2}\Big)^{\frac{1}{p-1}} x^{-\frac{2}{p-1}}.$$

Seek solutions of the form $u(x,t) = v_\infty(x)\,\phi(\zeta)$ with $\zeta = \ln(x/\sqrt t)$. The self-similar profile $\phi$ must solve

$$\phi'' + \Big(\frac{e^{2\zeta}}{2} - \frac{p+3}{p-1}\Big)\phi' + \frac{2(p+1)}{(p-1)^2}\,\phi\,(1 - \phi^{p-1}) = 0 \qquad (\zeta \in \mathbb{R}),$$

$$\phi(\zeta) \to 1,\ \phi'(\zeta) \to 0 \ \text{ as } \zeta \to -\infty; \qquad \phi(\zeta) \to 0,\ \phi'(\zeta) \to 0 \ \text{ as } \zeta \to +\infty.$$

**Theorem.** For every $p > 1$ there is a unique weak solution $\phi$ of the profile equation such that $\phi - \eta \in H^1(\mathbb{R}, d\mu)$ for every smooth $\eta$ with $\eta = 1$ on $(-\infty, 0]$ and $\eta = 0$ on $[1, \infty)$, where $H^1(\mathbb{R}, d\mu)$ is the weighted Sobolev space with

$$d\mu(\zeta) = \rho(\zeta)\,d\zeta, \qquad \rho(\zeta) = \exp\Big\{\frac{e^{2\zeta}}{4} - \frac{p+3}{p-1}\,\zeta\Big\}.$$

 Moreover $\phi \in C^\infty(\mathbb{R})$ solves the equation classically, $0 < \phi < 1$, $\phi$ is strictly decreasing, and $\phi$ satisfies both limit conditions.

The corresponding $u = v_\infty(x)\phi(\ln(x/\sqrt t))$ is an ultra-singular self-similar solution: infinite at $x = 0$ for all $t > 0$, yet vanishing at $t = 0$ for every $x > 0$.

## Expansion

Multiplying by $\rho$ turns the equation into $(\rho\phi')' + \frac{2(p+1)}{(p-1)^2}\rho\,\phi(1 - \phi^{p-1}) = 0$, since $\rho'/\rho$ is exactly the drift coefficient, so solutions are critical points of a weighted energy. Existence follows by minimization over the affine space $\eta + H^1(\mathbb{R}, d\mu)$, where weighted Poincaré inequalities on half-lines $[R,\infty)$ and $(-\infty, R]$ give coercivity; uniqueness uses a convexity property of the energy along suitable interpolating paths between two solutions. The rapidly growing drift $e^{2\zeta}/2$ forces superexponential decay of $\phi$ at $+\infty$, while at $-\infty$ the profile approaches the stable state $\phi = 1$ of the reaction term $\phi(1 - \phi^{p-1})$.

## Sources

- P. V. Gordon and C. B. Muratov, "Self-similarity and long-time behavior of solutions of the diffusion equation with nonlinear absorption and a boundary source", arXiv:1201.2243 (2012), Section 2 (similarity ansatz, profile equation, Theorem 1 and Lemma 1), <https://doi.org/10.48550/arXiv.1201.2243>.
