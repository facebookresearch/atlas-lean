# Invading and receding Fisher–Stefan travelling waves

**Model.** In nondimensional form, a population density $u(x,t)$ occupies $0 < x < L(t)$ and satisfies

$$\frac{\partial u}{\partial t} = \frac{\partial^2 u}{\partial x^2} + u(1-u),\qquad \frac{\partial u}{\partial x}(0,t) = 0,\qquad u(L(t),t) = 0,$$

with the moving edge governed by the one-phase Stefan condition

$$\frac{dL}{dt} = -\kappa\,\frac{\partial u}{\partial x}(L(t),t),$$

where $\kappa \in \mathbb R$ is the single parameter. With dimensional diffusivity $\hat D$, growth rate $\hat\lambda$, carrying capacity $\hat K$ and the dimensional law $d\hat L/d\hat t = -\hat\kappa\,\partial\hat u/\partial\hat x$ for the dimensional density $\hat u$, the scalings $x = \hat x\sqrt{\hat\lambda/\hat D}$, $t = \hat\lambda\hat t$, $u = \hat u/\hat K$ give $\kappa = \hat\kappa\hat K/\hat D$ (the source writes $\kappa = \hat\kappa/\hat D$, which corresponds to measuring $\hat\kappa$ against the gradient of the normalised density $\hat u/\hat K$).

**Travelling-wave problem.** A travelling wave on the half-line is a profile $U(z)$, $z = x - ct$, with the front at $z = 0$ and the left boundary sent to $z = -\infty$, solving

$$U'' + cU' + U(1-U) = 0\quad(-\infty < z < 0),\qquad U(-\infty) = 1,\quad U(0) = 0,\quad c = -\kappa\,U'(0).$$

In the phase plane $U' = V$, $V' = -cV - U(1-U)$ (the Fisher–KPP system), $(1,0)$ is a saddle for every $c$, and $(0,0)$ is a stable node for $c \ge 2$, a stable spiral for $0 < c < 2$, a linear centre for $c = 0$, an unstable spiral for $-2 < c < 0$ and an unstable node for $c \le -2$. A Fisher–Stefan wave of speed $c$ is the part of the trajectory through the saddle that lies in $U > 0$, $V < 0$ and is cut off where it meets the axis $U = 0$ at $(0, V^*)$; then $\kappa = -c/V^*$.

**Properties.**

1. Waves of the half-line problem exist for all signs of $c$: invading waves ($c > 0$) have $0 < c < 2$, including the trajectories near a stable spiral that the whole-line Fisher–KPP problem discards because they would make $U < 0$ beyond $z = 0$; receding waves ($c < 0$) exist for every $c < 0$.
2. Since $V^* < 0$, the wave invades ($c > 0$) iff $\kappa > 0$, recedes iff $\kappa < 0$, and is stationary iff $\kappa = 0$; numerically $c$ increases with $\kappa$.
3. Representative pairs from the phase plane: $c = 0.25, 0.5, 0.75, 1$ for $\kappa \approx 0.5859, 1.6879, 3.9823, 9.5315$, and $c = -0.5, -1, -2, -2.99$ for $\kappa \approx -0.5387, -0.7529, -0.9036, -0.9510$. Receding waves are much steeper at the edge than invading ones.

## Proof depends on

- [For c² < 4rD the linearization at U = 0 has two complex roots](../fisher-kpp-travelling-waves/char-root-iff-of-sq-lt.md)

## Expansion

Substituting $u = U(x - ct)$ turns the PDE into the travelling-wave ODE, and $L(t) = L_0 + ct$ turns the Stefan condition into $c = -\kappa U'(0)$. Linearizing at $(1,0)$ gives eigenvalues $\big(-c \pm \sqrt{c^2+4}\big)/2$ of opposite signs (a saddle), and at $(0,0)$ the eigenvalues $\big(-c \pm\sqrt{c^2-4}\big)/2$, whose type changes at $c = \pm2$ and $c = 0$; for $c^2 < 4$ they are the complex roots of $w^2 + cw + 1$. The truncation at $U = 0$ is what lets the model use trajectories that the Fisher–KPP problem on the whole line rejects, where [fronts exist only at or above the minimal speed](../fisher-kpp-travelling-waves/exists-is-front-iff.md): positivity is only required on $z < 0$. A finite domain $0 < x < L(t)$ is not covered by the half-line wave, whose slope never vanishes, so the Neumann condition at $x = 0$ fails for it. The source's finite-domain simulations (Figure 3 and Appendix B, with the compactly supported initial condition (7) at amplitudes $\alpha = 0.25, 0.5, 0.75, 1$) approach a travelling profile near the moving edge whose speed agrees with the half-line prediction for the given $\kappa$ and does not depend on the amplitudes tested. Inverting the map $c \mapsto \kappa(c)$ is useful because front speeds are measurable in experiments while $\kappa$ is not.

## Sources

- M. El-Hachem, S. W. McCue and M. J. Simpson, "Invading and receding sharp-fronted travelling waves", Bulletin of Mathematical Biology (2021), <https://doi.org/10.1007/s11538-021-00862-y>. Numbering as in the preprint arXiv:2008.00662v3 (<https://arxiv.org/abs/2008.00662>): Sections 2–2.1, Equations (1)–(7); Sections 3.1–3.2, Equations (8)–(12), Figures 3–4; Appendix B.
