# Equilibria of a discrete two-stage Trojan Y-chromosome model

**Model.** Let $x_t$, $y_t$, $z_t$ be adult females, males and supermales at the start of generation $t$. Each generation has an egg stage, in which females produce $c$ offspring that survive the egg stage, fathered by males or supermales in proportion to their numbers, $f_y(y,z) = y/(y+z)$ and $f_z(y,z) = z/(y+z)$, and a maturity stage, in which juveniles survive with density-dependent probability $\rho(cx)$, a fraction $\alpha \in (0,1)$ of surviving offspring of ordinary males become females, all offspring of supermales become males, and $\mu \ge 0$ supermales are released. The survival function satisfies $0 \le \rho \le 1$, $\rho$ decreasing, $\rho(0) = 1$, $\rho(w) \to 0$ as $w \to \infty$. With adult mortalities $m_x, m_y, m_z \in (0,1)$,

$$x_{t+1} = (1-m_x)x_t + \alpha c\rho(cx_t)f_y(y_t,z_t)x_t,$$

$$y_{t+1} = (1-m_y)y_t + (1-\alpha)c\rho(cx_t)f_y(y_t,z_t)x_t + c\rho(cx_t)f_z(y_t,z_t)x_t,$$

$$z_{t+1} = (1-m_z)z_t + \mu.$$

**Theorem 4.1.** The extinction equilibrium $(0, 0, \mu/m_z)$ always exists.

**Theorem 4.3.** The extinction equilibrium is locally asymptotically stable: the Jacobian there is lower triangular with eigenvalues $1 - m_x$, $1 - m_y$, $1 - m_z$, all in $(0,1)$.

**Positive equilibria (Theorem 4.2).** At a positive equilibrium $z = \mu/m_z$, and with $u = cx$, $\lambda = \mu m_x m_y/(\alpha c m_z)$ and $\beta = m_x/c$, the female abundance solves

$$\frac{\lambda}{u} = \big(\rho(u) - \alpha\beta\big)\big(\rho(u) - \beta\big), \qquad y = \frac{\mu m_x}{m_z\big(\alpha c\rho(u) - m_x\big)}.$$

Assuming $0 < \alpha\beta < \beta < 1$, the right side tends to $\alpha\beta^2 > 0$ as $u \to \infty$ while the left side tends to $0$, and the left side tends to $+\infty$ as $u \to 0^+$, so the equation always has a positive root; the paper concludes that a positive equilibrium always exists, and the curves can meet once, twice (tangency) or three times. The corresponding male abundance is positive when $\alpha c\rho(u) > m_x$.

**Without releases.** If $\mu = 0$, supermales vanish and the origin of the reduced $(x,y)$ system has eigenvalues $1 - m_x + \alpha c\rho(0)$ and $1 - m_y$, so it is locally asymptotically stable exactly when $m_x > \alpha c\rho(0) = \alpha c$: a small population dies out when females die faster than they produce surviving daughters.

## Expansion

Because $\rho(0) = 1$ and supermales stabilize at $\mu/m_z > 0$, near extinction every newborn has a supermale father with probability close to $1$, so no daughters are produced and the female equation contracts by $1 - m_x$; this is why releases make extinction locally stable for any fecundity. Far from extinction, density-dependent juvenile survival caps recruitment, and a positive equilibrium coexists with the stable extinction state, giving bistability: numerically, whether releases eradicate the population depends on fecundity, the release size and the initial abundances, as shown by separatrices and bifurcation diagrams in the release rate.

## Depends on

- [Blow-up of the classical Trojan Y-chromosome ODE model](blow-up-of-the-classical-trojan-y-chromosome-ode-model.md)

## Sources

- D. K. Mallawa Arachchi, R. D. Parshad, C. Kadelka, "Invasive species control via a discrete model for the Trojan Y-chromosome strategy" (2025), Section 3 (two-stage model and conditions on $\rho$), Section 4 (Theorems 4.1, 4.2 and 4.3, the key equilibrium equation and the release-free stability condition, numerical bifurcation study), <https://doi.org/10.48550/arXiv.2506.14023>.
