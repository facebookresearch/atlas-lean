# Threshold dynamics of the delayed virus-versus-virus HIV model

**Model.** A genetically modified (recombinant) virus that infects only HIV-infected cells is used against HIV-1. Let $x$ be healthy CD4 T cells, $y$ HIV-infected cells, $z$ doubly infected cells, $v$ HIV virions and $w$ recombinant virions. With an eclipse-phase delay $\tau \ge 0$, during which a contacted cell survives with probability $e^{-a\tau}$,

$$\dot x = \lambda - dx - \beta xv, \qquad \dot y = \beta e^{-a\tau}x(t-\tau)v(t-\tau) - ay - \alpha wy, \qquad \dot z = \alpha wy - bz,$$

$$\dot v = ky - pv, \qquad \dot w = cz - qw,$$

with positive parameters. Doubly infected cells release recombinant virus at rate $c$. Solutions with non-negative initial data stay non-negative and bounded.

**Equilibria and thresholds.** Define

$$\mathcal{R}_0 = \frac{k\beta\lambda}{adp}e^{-a\tau}, \qquad R_1 = 1 + \frac{\beta bkq}{\alpha cdp}.$$

The equilibria are the disease-free $E_0 = (\lambda/d, 0, 0, 0, 0)$; the single-infection equilibrium (HIV only)

$$E_s = \Big(\frac{ap}{\beta k e^{-a\tau}},\ \frac{k\beta\lambda e^{-a\tau} - adp}{\beta ak},\ 0,\ \frac{k\beta\lambda e^{-a\tau} - adp}{\beta ap},\ 0\Big),$$

which is biologically meaningful iff $\mathcal{R}_0 > 1$; and the double-infection equilibrium $E_d$, with $y_d = bq/(\alpha c)$ and $v_d = bkq/(\alpha cp)$, which is meaningful iff $\mathcal{R}_0 > R_1$. The threshold $R_1$ does not depend on the delay, whereas $\mathcal{R}_0$ decreases as $\tau$ grows.

**Theorem (disease-free state).** If $\mathcal{R}_0 < 1$, then $E_0$ is globally asymptotically stable (neither virus can invade). If $\mathcal{R}_0 > 1$, then $E_0$ is unstable and $E_s$ appears.

**Theorem (single infection).** If $1 < \mathcal{R}_0 < R_1$, then $E_s$ is globally asymptotically stable: HIV persists and the recombinant virus dies out. If $\mathcal{R}_0 > R_1$, then $E_s$ is unstable.

**Theorem (double infection).** There is $R_2 > R_1$ such that $E_d$ is asymptotically stable for $R_1 < \mathcal{R}_0 < R_2$. Taking $\tau$ as the bifurcation parameter, if the first critical value $R_h > R_1$ at which the characteristic equation at $E_d$ acquires purely imaginary roots satisfies the transversality conditions, then $E_d$ loses stability at $\mathcal{R}_0 = R_h$ through a Hopf bifurcation and a family of limit cycles appears.

Thus the equilibria exchange stability through transcritical bifurcations at $\mathcal{R}_0 = 1$ and $\mathcal{R}_0 = R_1$. Since the delay lowers $\mathcal{R}_0$, it can move the system from the oscillatory regime back to a stable equilibrium.

## Expansion

At $E_0$ the linearization factors, and the $(y, v)$ block has characteristic equation $(\xi + a)(\xi + p) = k\beta(\lambda/d)e^{-a\tau}e^{-\xi\tau}$, which has a positive root iff $\mathcal{R}_0 > 1$. Global stability of $E_0$ uses the Lyapunov functional

$$V_0 = \frac{e^{-a\tau}}{2}\Big(x - \frac{\lambda}{d}\Big)^2 + \frac{\lambda}{d}y + \frac{\lambda}{d}z + \frac{a\lambda}{dk}v + \frac{b\lambda}{cd}w + \frac{\lambda\beta}{d}e^{-a\tau}\int_{t-\tau}^{t}x(s)v(s)\,ds.$$

For $E_s$ one uses the Volterra-type functional

$$V_1 = e^{-a\tau}(x - x_s\ln x) + (y - y_s\ln y) + z + \frac{a}{k}(v - v_s\ln v) + \frac{b}{c}w,$$

plus $\beta x_s v_s e^{-a\tau}\int_{t-\tau}^{t}\big(\frac{x(s)v(s)}{x_s v_s} - \ln\frac{x(s)v(s)}{x_s v_s}\big)ds$. Along solutions, the recombinant terms of its derivative collapse to $w\,(\alpha y_s - bq/c)$, which is non-positive exactly when $\alpha c y_s \le bq$, i.e. when $\mathcal{R}_0 \le R_1$. Local stability of $E_d$ near $\mathcal{R}_0 = R_1$ follows from Routh–Hurwitz determinants of the $\tau$-dependent characteristic polynomial and a continuity argument.

## Sources

- Y. Tian, Y. Bai and P. Yu, "Impact of delay on HIV-1 dynamics of fighting a virus with another virus", arXiv:1403.3958 (2014): model, equilibria and Theorem 2.1 (Section 2); Theorems 3.1–3.2 (disease-free equilibrium, Section 3); Theorems 4.1–4.2 (single-infection equilibrium, Section 4); Theorem 5.1 and the Hopf bifurcation analysis (double-infection equilibrium, Section 5). <https://doi.org/10.48550/arXiv.1403.3958>. Published version: Mathematical Biosciences and Engineering 11(5) (2014), 1181–1198, <https://doi.org/10.3934/mbe.2014.11.1181>; locators above refer to the arXiv version.
