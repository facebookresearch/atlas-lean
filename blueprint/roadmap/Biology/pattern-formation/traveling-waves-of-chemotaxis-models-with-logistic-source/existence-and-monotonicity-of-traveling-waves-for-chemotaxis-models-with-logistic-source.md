# Existence and monotonicity of traveling waves for chemotaxis models with logistic source

**Model.** Let $m, \alpha, \gamma \ge 1$ and $\chi \in \mathbb{R}$, and consider on $x \in \mathbb{R}$

$$u_t = u_{xx} - \chi(u^m v_x)_x + u(1 - u^\alpha), \qquad 0 = v_{xx} - v + u^\gamma,$$

where $u$ is a population density and $v$ the concentration of a chemical it produces; $\chi > 0$ is chemoattraction and $\chi < 0$ chemorepulsion. A traveling wave connecting $(1,1)$ and $(0,0)$ is a solution $(U(x - ct), V(x - ct))$ with $(U,V) \to (1,1)$ as $x \to -\infty$ and $(U,V) \to (0,0)$ as $x \to \infty$. For $c > 2$ put $\kappa = (c - \sqrt{c^2-4})/2$, the slower decay rate of the linearization $U'' + cU' + U = 0$ at $0$.

**Theorem.**
1. *(Chemorepulsion: monotone waves.)* Let $\alpha \le m + \gamma - 1$ and $\chi \le 0$. For every

$$c > c^*_{\chi,m,\gamma} = \max\Big\{\frac1m + m,\ \frac{1}{\sqrt{m\gamma|\chi| + \gamma^2|\chi| + \gamma^2}} + \sqrt{m\gamma|\chi| + \gamma^2|\chi| + \gamma^2}\Big\}$$

there is a traveling wave of speed $c$ connecting $(1,1)$ and $(0,0)$ with $0 < U < \max\{1, e^{-\kappa x}\}$, $U' \le 0$ and $V' \le 0$; moreover, for every $\kappa_1$ with $\kappa < \kappa_1 < \min\{(1+\alpha)\kappa, m\kappa + \tfrac12, 1\}$,

$$\lim_{x\to\infty} e^{(\kappa_1 - \kappa)x}\Big(\frac{U(x)}{e^{-\kappa x}} - 1\Big) = 0.$$

2. *(Weak chemoattraction.)* Let $\alpha = m + \gamma - 1$ and $0 \le \chi < \min\{\tfrac12, \chi^*\}$ with $\chi^* = \min\{1, (2m+2\gamma)/(m^2 + m + 2\gamma)\}$. For every $c > 2$ there is a traveling wave of speed $c$ connecting $(1,1)$ and $(0,0)$ with the same exponential tail and $0 < U < \min\{(1-\chi)^{-1/\alpha}, e^{-\kappa x}\}$.

At $\chi = 0$, $\gamma = 1$ the bound $c^*$ equals the Fisher–KPP minimal speed $2$, and as $\chi \to -\infty$ it grows like $\sqrt{|\chi|}$, reflecting that chemorepulsion speeds up the front. Along the way, solutions with bounded nonnegative data exist globally and are bounded for $\chi \le 0$ (and for $\chi > 0$ when $\alpha > m + \gamma - 1$, or $\alpha = m+\gamma-1$ with $\chi$ small), and the constant state $1$ attracts all solutions with positive infimum for $\chi \le 0$ and for $0 < \chi < \tfrac12$, $\alpha \ge m + \gamma - 1$.

## Depends on

- [Fisher–KPP fronts exist exactly at or above the minimal speed](../fisher-kpp-travelling-waves/exists-is-front-iff.md)

## Expansion

In the moving frame the wave is a stationary solution of $u_t = u_{xx} + cu_x - \chi(u^m v_x)_x + u(1-u^\alpha)$; it is constructed between explicit sub- and super-solutions, the latter of the form $\min\{M_\chi, e^{-\kappa x}\}$, where the speed condition keeps $e^{-\kappa x}$ a super-solution despite the nonlinear taxis term. The left limit $(1,1)$ follows from stability of the positive constant state, proved by showing that the spatial supremum (infimum) of $u$ decreases (increases) toward $1$ for $\chi < 0$, and by an ODE rectangle comparison for $0 < \chi < \tfrac12$. For $\chi \le 0$, comparison preserves monotonicity of the profile.

## Sources

- W. Shen, "Existence, uniqueness, stability, and monotonicity of traveling waves for repulsion/attraction chemotaxis models with logistic type source", arXiv:2605.04401 (2026), Theorem 1.1 (proved in Section 4), and Propositions 1.1 and 1.2 with Remark 1.1 (proved in Section 3), <https://doi.org/10.48550/arXiv.2605.04401>.
