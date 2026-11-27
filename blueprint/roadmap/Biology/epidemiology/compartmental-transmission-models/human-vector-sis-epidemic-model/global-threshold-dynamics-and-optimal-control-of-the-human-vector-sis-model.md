# Global threshold dynamics and optimal control of the human-vector SIS model

Let $x \in [0,1]$ be the fraction of infected humans, $y \ge 0$ the quantity of non-carrier vectors and $z \ge 0$ the quantity of carrier vectors. With human recovery rate $\gamma > 0$, human contagion rate $\beta_h > 0$, vector contagion rate $\beta_v > 0$, vector birth rate $\omega > 0$ and vector death rate $\mu > 0$, the HV-SIS model is

$$\dot x = -\gamma x + \beta_h(1 - x)z, \qquad \dot y = \omega - \mu y - \beta_v x y, \qquad \dot z = \beta_v x y - \mu z,$$

on $\mathcal{D} = \{x,y,z \ge 0,\ x \le 1\}$; the sets $\{y + z \le \omega/\mu\}$ and $\{y + z \ge \omega/\mu\}$ are both forward invariant. Define the epidemic threshold

$$\sigma_0 = \frac{\beta_h\beta_v\omega}{\gamma\mu^2} .$$

**Theorem.**

1. (Equilibria) The model has the disease-free equilibrium $(0, \omega/\mu, 0)$ and, if and only if $\sigma_0 > 1$, the endemic equilibrium

$$(\bar x, \bar y, \bar z) = \Big(\frac{\omega\beta_h\beta_v - \mu^2\gamma}{\omega\beta_h\beta_v + \mu\gamma\beta_v},\ \frac{\gamma\mu + \beta_h\omega}{\beta_h(\beta_v + \mu)},\ \frac{\omega\beta_h\beta_v - \mu^2\gamma}{\mu\beta_h\beta_v + \mu^2\beta_h}\Big).$$

2. (Global dynamics) If $\sigma_0 \le 1$, every trajectory converges to the disease-free equilibrium. If $\sigma_0 > 1$, every trajectory with $x(0) \ne 0$ or $z(0) \ne 0$ converges to the endemic equilibrium.
3. (Control) If vector control raises the vector death rate to $\mu + u_1$ and personal protection lowers the human contagion rate to $\beta_h - u_2$ ($u_1 \ge 0$, $0 \le u_2 \le \beta_h$), the controlled threshold is $\sigma_c = (\beta_h - u_2)\beta_v\omega / (\gamma(\mu + u_1)^2)$ and the same dichotomy holds with $\sigma_c$. For a differentiable cost $C(u_1,u_2)$ increasing in both arguments, the cheapest controls guaranteeing eradication ($\sigma_c \le 1$) satisfy, with a multiplier $\lambda$,

$$\partial_{u_1}C - 2\lambda\gamma(\mu + u_1) = 0, \qquad \partial_{u_2}C - \lambda\beta_v\omega = 0, \qquad (\beta_h - u_2)\beta_v\omega = \gamma(\mu + u_1)^2 .$$

For linear cost $C = c_1u_1 + c_2u_2$ and $\sigma_0 > 1$ the optimum is a single-measure policy: $u_1^* = \sqrt{\beta_h\beta_v\omega/\gamma} - \mu$, $u_2^* = 0$ unless $(c_1,c_2) \in \mathcal{C}$, in which case $u_1^* = 0$, $u_2^* = (\beta_h\beta_v\omega - \gamma\mu^2)/(\beta_v\omega)$, where

$$\mathcal{C} = \Big\{(c_1,c_2) : \frac{c_1}{c_2} > \frac{2\gamma\mu}{\beta_v\omega},\ \Big(\frac{c_1}{c_2}\beta_v\omega - \gamma\mu\Big)^2 \ge \beta_h\beta_v\gamma\omega\Big\}.$$

## Expansion

The total vector population $w = y + z$ obeys $\dot w = \omega - \mu w$ and converges to $\omega/\mu$, so the dynamics reduce asymptotically to the planar system in $(x,z)$ with $y = \omega/\mu - z$. That system is cooperative (infected humans increase carrier production and carriers increase human infections), so trajectories are eventually monotone and converge to equilibria; the Jacobian at the disease-free equilibrium has spectral abscissa of the sign of $\sigma_0 - 1$, and the endemic equilibrium, when it exists, is the unique positive one and is locally stable. Because the cost increases in both controls, the eradication constraint $\sigma_c \le 1$ is active at the optimum, and the Karush–Kuhn–Tucker conditions on the curve $u_2 = \beta_h - \gamma(\mu + u_1)^2/(\beta_v\omega)$ give the stated system. That curve is concave in $u_1$, so a linear cost restricted to it is minimized at one of its two endpoints, pure vector control or pure personal protection; comparing the two endpoint costs gives the set $\mathcal{C}$.

## Sources

- Lorenzo Zino, Alessandro Casu, Alessandro Rizzo, "A Human-Vector Susceptible–Infected–Susceptible Model for Analyzing and Controlling the Spread of Vector-Borne Diseases", in 2025 European Control Conference (ECC) (2025), 1219–1224, <https://doi.org/10.23919/ecc65951.2025.11186881>. Published version of arXiv:2510.14787, cited next; locators there refer to the arXiv version.
- Lorenzo Zino, Alessandro Casu, Alessandro Rizzo, "A Human-Vector Susceptible-Infected-Susceptible Model for Analyzing and Controlling the Spread of Vector-Borne Diseases", arXiv (2025). Equation (model), Lemma 1, Proposition 1, Theorem 1, Corollary 1, Theorem 2, Corollary 2. <https://doi.org/10.48550/arXiv.2510.14787>
