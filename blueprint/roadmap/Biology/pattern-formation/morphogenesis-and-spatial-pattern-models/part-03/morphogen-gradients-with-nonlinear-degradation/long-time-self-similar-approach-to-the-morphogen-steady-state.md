# Long-time self-similar approach to the morphogen steady state

**Setting.** Let a morphogen be produced at constant flux $\alpha > 0$ at $x = 0$, diffuse, and degrade with nonlinear rate $u^p$, $p > 1$:

$$u_t = u_{xx} - u^p \ \ (x,t) \in [0,\infty) \times (0,\infty), \qquad u_x(0,t) = -\alpha, \qquad u(x,0) = 0.$$

The steady state $v$, solving $v_{xx} = v^p$, $v_x(0) = -\alpha$, $v(\infty) = 0$, is explicit:

$$v(x) = \Big(\frac{2(p+1)}{(p-1)^2}\Big)^{\frac{1}{p-1}} (a + x)^{-\frac{2}{p-1}}, \qquad a = \frac{2^{\frac{p}{p+1}}(p+1)^{\frac{1}{p+1}}}{p-1}\,\alpha^{-\frac{p-1}{p+1}},$$

and $u(x,t) \uparrow v(x)$ as $t \to \infty$ for each $x$, but not uniformly in $x$. Let $\phi$ be the unique decreasing self-similar profile of the problem with infinitely strong source (solution of $\phi'' + (e^{2\zeta}/2 - \frac{p+3}{p-1})\phi' + \frac{2(p+1)}{(p-1)^2}\phi(1 - \phi^{p-1}) = 0$ with $\phi(-\infty) = 1$, $\phi(+\infty) = 0$).

**Theorem.** Set

$$F(\zeta, t) = \frac{u(x,t)}{v(x)}, \qquad \zeta = \ln\frac{x}{\sqrt t}.$$

Then $\lim_{t \to \infty} F(\zeta, t) = \phi(\zeta)$ for every $\zeta \in \mathbb{R}$, and there is a constant $b > 0$ such that

$$\phi\big(\ln(e^\zeta + b\,t^{-1/2})\big) \le F(\zeta, t) \le \phi(\zeta)$$

for all $\zeta$ and $t > 0$. So at large times the fraction of the steady-state concentration reached at position $x$ depends only on $x/\sqrt t$: the steady gradient is established behind a front moving diffusively, $x \sim \sqrt t$, independently of the source strength.

## Expansion

Both bounds are obtained from the comparison principle for the operators $P[u] = u_t - u_{xx} + u^p$ in the interior and $Q[u] = u_x + \alpha$ at $x = 0$: super- and subsolutions with zero initial data are built from the steady state $v$ and the self-similar profile $\phi$, the latter with the argument shifted by $b\,t^{-1/2}$. The shift becomes negligible as $t \to \infty$, which squeezes $F$ to $\phi$. For fixed $x$ the time to approach $v(x)$ thus scales like $x^2$, the diffusive time scale.

## Depends on

- [Ultra-singular self-similar solution of diffusion with nonlinear absorption](ultra-singular-self-similar-solution-of-diffusion-with-nonlinear-absorption.md)

## Sources

- P. V. Gordon and C. B. Muratov, "Self-similarity and long-time behavior of solutions of the diffusion equation with nonlinear absorption and a boundary source", arXiv:1201.2243 (2012), Section 1 (problem and explicit steady state) and Section 3 (Theorem 2), <https://doi.org/10.48550/arXiv.1201.2243>.
