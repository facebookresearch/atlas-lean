# Uniqueness and stability of fast traveling waves for chemotaxis models with logistic source

**Model.** Let $m, \alpha, \gamma \ge 1$ and $\chi \in \mathbb{R}$, and consider on $x \in \mathbb{R}$

$$u_t = u_{xx} - \chi(u^m v_x)_x + u(1 - u^\alpha), \qquad 0 = v_{xx} - v + u^\gamma,$$

where $u$ is a population density and $v$ the concentration of a chemical it produces; $\chi > 0$ is chemoattraction and $\chi < 0$ chemorepulsion. A traveling wave connecting $(1,1)$ and $(0,0)$ is a solution $(U(x - ct), V(x - ct))$ with $(U,V) \to (1,1)$ as $x \to -\infty$ and $(U,V) \to (0,0)$ as $x \to \infty$. For $c > 2$ put $\kappa = (c - \sqrt{c^2-4})/2$, the slower decay rate of the linearization $U'' + cU' + U = 0$ at $0$.

**Theorem.** Assume $\chi < 0$ and $\alpha \le m + \gamma - 1$, or $0 \le \chi < \chi^* = \min\{1, (2m+2\gamma)/(m^2+m+2\gamma)\}$ and $\alpha = m + \gamma - 1$. Let $M_\chi = 1$ if $\chi < 0$ and $M_\chi = (1-\chi)^{-1/\alpha}$ otherwise. There is a speed threshold $c^{**}_{\chi,m,\alpha,\gamma} > 1 + |\chi|^{1/6} + (1 + |\chi|^{1/6})^{-1}$, with $c^{**} - (\gamma + 1/\gamma) = O(|\chi|^{1/6})$ as $\chi \to 0$, such that for $c > c^{**}$ the following hold for traveling waves $(U,V)$ of speed $c$ connecting $(1,1)$ and $(0,0)$ that satisfy $0 < U < \min\{M_\chi, e^{-\kappa x}\}$ and the tail condition $e^{(\kappa_1-\kappa)x}(U(x)e^{\kappa x} - 1) \to 0$ for some $\kappa_1 \in (\kappa, 1)$:
1. *(Uniqueness.)* There is at most one such wave: any two coincide.
2. *(Stability.)* For every $\eta \in (\kappa, (1 + |\chi|^{1/6})^{-1})$ and every bounded uniformly continuous $u_0 \ge 0$ with $\liminf_{x\to-\infty} u_0(x) > 0$ and $\int_{\mathbb{R}} e^{2\eta x}|u_0 - U|^2\,dx < \infty$,

$$\lim_{t\to\infty}\int_{\mathbb{R}} e^{2\eta x}|u(t,x) - U(x - ct)|^2\,dx = 0 \qquad\text{and}\qquad \lim_{t\to\infty}\sup_{x\in\mathbb{R}}|u(t,x) - U(x - ct)| = 0.$$

## Depends on

- [Existence and monotonicity of traveling waves for chemotaxis models with logistic source](existence-and-monotonicity-of-traveling-waves-for-chemotaxis-models-with-logistic-source.md)

## Expansion

A priori estimates for any wave with $0 < U \le \min\{M_\chi, e^{-\kappa x}\}$ bound $V$ and $V_x$ by $M_\chi^\gamma$ and control the tails. In the moving frame, the perturbation $w = u - U$ is estimated in the exponentially weighted space $L^2(e^{2\eta x}dx)$ with $\eta > \kappa$: the weight turns the convective term into damping, and for speeds above $c^{**}$ the chemotactic coupling, controlled through the elliptic equation for $v$, is dominated, so the weighted norm of $w$ tends to zero. Uniqueness follows by applying this convergence with one wave as the initial datum of the other.

## Sources

- W. Shen, "Existence, uniqueness, stability, and monotonicity of traveling waves for repulsion/attraction chemotaxis models with logistic type source", arXiv:2605.04401 (2026), Theorems 1.2 and 1.3, proved in Section 5, <https://doi.org/10.48550/arXiv.2605.04401>.
