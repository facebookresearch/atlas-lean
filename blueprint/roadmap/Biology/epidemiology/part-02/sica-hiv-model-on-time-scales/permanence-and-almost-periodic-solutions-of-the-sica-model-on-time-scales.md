# Permanence and almost periodic solutions of the SICA model on time scales

**Model.** Let $\mathbb T^+$ be a time scale (a nonempty closed subset of $(0,\infty)$), with delta derivative $x^\Delta$ and forward jump $x^\sigma(t) = x(\sigma(t))$; for $\mathbb T = \mathbb R$ these are $x'$ and $x$, for $\mathbb T = h\mathbb Z$ they are a forward difference quotient and $x(t+h)$. The SICA dynamics of susceptibles $x_1$, untreated HIV-infected $x_2$, chronically infected under treatment $x_3$ and AIDS cases $x_4$ is

$$x_1^\Delta = \Lambda - \beta\lambda(t)x_1^\sigma - \nu x_1^\sigma, \qquad x_2^\Delta = \beta\lambda(t)x_1 - (\rho + \phi + \nu)x_2^\sigma + \gamma x_4 + \omega x_3,$$

$$x_3^\Delta = \phi x_2 - (\omega + \nu)x_3^\sigma, \qquad x_4^\Delta = \rho x_2 - (\gamma + \nu + d)x_4^\sigma,$$

with recruitment $\Lambda$, transmission rate $\beta$, natural death $\nu$, treatment rate $\phi$, treatment default rates $\rho$ (from $I$) and $\omega$ (from $C$), AIDS treatment rate $\gamma$ and AIDS death rate $d$, all positive, and contact function $\lambda(t) = \frac{\beta}{N}(x_2 + \eta_Cx_3 + \eta_Ax_4)$ with $0\le\eta_C\le1$, $\eta_A\ge1$.

**Hypotheses.** $(H_1)$: $\lambda$ is almost periodic with $0 < \lambda^L\le\lambda(t)\le\lambda^U$. $(H_2)$: with $m, M$ the permanence bounds below,

$$\Gamma_2 := \max\Big\{\beta\lambda^U + \tfrac{\beta^2M}{2m},\ \rho + \phi,\ \omega + \tfrac{\beta^2M}{2m}\eta_C,\ \gamma + \tfrac{\beta^2M}{2m}\eta_A\Big\} < \Gamma_1 := \min\{\beta\lambda^L + \nu,\ \rho + \phi + \nu,\ \omega + \nu,\ \gamma + \nu + d\},$$

with $\Gamma_1,\Gamma_2$ positively regressive on $\mathbb T$.

**Theorem.**

1. (Permanence.) Under $(H_1)$, every positive solution is eventually bounded, $x_i(t)\le M$ for $t\ge T$, and the system is permanent: there are $0 < m\le M$ with $m\le x_i(t)\le M$ eventually for $i = 1,\dots,4$. On $\mathbb T = \mathbb R$, moreover, $N(t_0)\le\Lambda/\nu$ implies $N(t)\le\Lambda/\nu$ for all $t\ge t_0$.
2. (Almost periodic attractor.) Under $(H_1)$ and $(H_2)$, the system has a unique almost periodic solution with values in $\{m\le x_i\le M\}$, and it is uniformly asymptotically stable.

The source states that $N\le\Lambda/\nu$ is preserved on every time scale and places the almost periodic solution in the invariant set $\{m\le x_i\le M,\ N\le\Lambda/\nu\}$. Both fail on $\mathbb T = h\mathbb Z$: on $\mathbb Z$ with $\Lambda=\beta=1$, $\nu=0.1$, $\rho=\phi=\omega=\gamma=d=0.01$, $\eta_C=\eta_A=1$, $\lambda\equiv0.1$ and $x(t_0)=(8.9,1,0.05,0.05)$, so that $N=10=\Lambda/\nu$, one step gives $N=10.046$. The page therefore restricts the first claim to $\mathbb T=\mathbb R$ and drops the second.

On $\mathbb T = \mathbb R$ this gives a globally attracting almost periodic HIV/AIDS regime for seasonally or irregularly forced transmission; on $\mathbb T = \mathbb Z$ it gives the same conclusion for the discrete-time model.

## Expansion

Permanence uses a comparison lemma on time scales: an inequality $y^\Delta\ge b - ay^\sigma$ with $-a$ positively regressive implies $y(t)\ge\frac ba\big[1 + (\frac{ay(t_0)}{b} - 1)e_{\ominus a}(t,t_0)\big]$, and similarly for upper bounds, applied successively to the total population and to each compartment. For the almost periodic solution one uses the time-scale version of a Lyapunov criterion: if a function $V(t,x,z)$ comparable to $\|x - z\|$, Lipschitz in its state arguments, decays along pairs of solutions in the product system, and a bounded solution exists, then there is a unique uniformly asymptotically stable almost periodic solution. For a Lyapunov function measuring the distance between two solutions, the decay rate is at least $\Gamma_1 - \Gamma_2$, where $\Gamma_1$ collects the outflow rates and $\Gamma_2$ bounds the cross-coupling terms (including the nonlinear incidence, controlled by $M/m$), which is why $(H_2)$ is needed.

## Sources

- Zahra Belarbi, Benaoumeur Bayour, Delfim F. M. Torres, "Uniform stability of dynamic SICA HIV transmission models on time scales", arXiv (2024). Section 1 (model), Section 2 (Lemmas 2.4 and 2.8), Section 3 (hypothesis $(H_1)$, Lemmas 3.1–3.2), Section 4 (hypothesis $(H_2)$, Theorem 4.1). <https://doi.org/10.48550/arXiv.2406.18596>. Published version: Applicationes Mathematicae 51(2) (2024), 163–177, <https://doi.org/10.4064/am2521-6-2024>; locators above refer to the arXiv version.
