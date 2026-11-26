# Global stability of the SIS model with saturating contact rate

**Model.** Let $S(t), I(t) \ge 0$ be susceptible and infectious numbers, $N = S + I$, and

$$\frac{dS}{dt} = \Lambda - \frac{\beta S I}{h(N)} - \mu S + \gamma I, \qquad \frac{dI}{dt} = \frac{\beta S I}{h(N)} - (\mu + \delta + \gamma) I,$$

with recruitment $\Lambda > 0$, natural death rate $\mu > 0$, disease-induced death rate $\delta \ge 0$, recovery rate $\gamma > 0$, transmission coefficient $\beta > 0$, and

$$h(N) = 1 + bN + \sqrt{1 + 2bN}, \qquad b > 0,$$

so that the contact rate $C(N) = bN/h(N)$ saturates in $N$. The basic reproduction number is

$$\mathcal{R}_0 = \frac{\Lambda\beta}{\mu(\mu + \delta + \gamma)\, h(\Lambda/\mu)}.$$

There is always a disease-free equilibrium $E_0 = (\Lambda/\mu, 0)$, and a unique endemic equilibrium $E_*$ exists iff $\mathcal{R}_0 > 1$.

**Theorem.**

1. If $S(0) \ge 0$ and $I(0) > 0$ then $S(t), I(t) > 0$ for all $t > 0$.
2. If $\mathcal{R}_0 < 1$, then $E_0$ is globally asymptotically stable.
3. If $\mathcal{R}_0 > 1$, then $E_*$ is globally asymptotically stable on $\{S \ge 0, I > 0\}$.

## Expansion

In the variables $(I, N)$ the system reads $\dot I = f(I,N) = \beta(N - I)I/h(N) - (\mu + \delta + \gamma)I$, $\dot N = g(I,N) = \Lambda - \mu N - \delta I$. With the Dulac function $D = 1/I$,

$$\frac{\partial(Df)}{\partial I} + \frac{\partial(Dg)}{\partial N} = -\frac{\beta}{h(N)} - \frac{\mu}{I} < 0 \quad (I, N > 0),$$

so by the Bendixson–Dulac criterion there are no periodic orbits or graphics in the open quadrant; since $E_0$ is a saddle repelling into the interior when $\mathcal{R}_0 > 1$, the Poincaré–Bendixson theorem sends every interior orbit to $E_*$. For $\mathcal{R}_0 < 1$ the disease-free state is globally stable, shown both with the Lyapunov function $V = l_1 I + \tfrac12 l_2 (N - \Lambda/\mu)^2$ for suitable $l_1, l_2 > 0$ and with the Castillo-Chavez–Feng–Huang threshold criterion.

## Sources

- M. T. Hoang, "A Mathematical Study of an SIS Epidemic Model: Global Asymptotic Stability Analysis and Construction of Nonstandard Finite Difference Schemes", arXiv:2609.29567 (2026), Section 2, Theorems 2.1–2.4, <https://doi.org/10.48550/arXiv.2609.29567>.
