# Approximate aggregation of the primary–opportunistic coinfection model

**Full model.** Hosts are susceptible ($S$), primary-infected only ($U$) or coinfected ($V$). The opportunistic disease is an SIS process with frequency-dependent transmission $\lambda$ and recovery $\delta$ among primary-infected hosts, running on a fast time $\tau$; demography (fertility $r$ reduced by factors $0<a_V<a_U<1$, mortality $m$, competition coefficients $c_{XY}$) and the primary disease (density-dependent transmission $\beta_U,\beta_V$, recovery $\gamma$, extra mortality $\mu_U,\mu_V$) act on the slow time $t=\varepsilon\tau$:

$$
\begin{aligned}
\frac{dS}{d\tau} &= \varepsilon\big[rS + a_UrU + a_VrV - mS - (c_{SS}S+c_{SU}U+c_{SV}V)S - \beta_USU - \beta_VSV + \gamma U\big],\\
\frac{dU}{d\tau} &= -\frac{\lambda UV}{U+V} + \delta V + \varepsilon\big[-mU - (c_{US}S+c_{UU}U+c_{UV}V)U + \beta_USU + \beta_VSV - \gamma U - \mu_UU\big],\\
\frac{dV}{d\tau} &= \frac{\lambda UV}{U+V} - \delta V + \varepsilon\big[-mV - (c_{VS}S+c_{VU}U+c_{VV}V)V - \mu_VV\big].
\end{aligned}
$$

**Fast equilibrium.** With $I=U+V$ held fixed, the fast equation $\frac{dV}{d\tau}=\frac{\lambda(I-V)V}{I}-\delta V$ drives $V(\tau)\to\nu^*I$ for $V(0)>0$, where

$$
\nu^* = \begin{cases} 0, & \delta\ge\lambda,\\ 1-\delta/\lambda, & \delta<\lambda.\end{cases}
$$

**Aggregated system.** Substituting $V=\nu^*I$ into the slow equations for $S$ and $I$ gives

$$
\begin{aligned}
\frac{dS}{dt} &= rS + \bar a rI - mS - (c_{SS}S+\bar c_{SI}I)S - \bar\beta SI + \bar\gamma I,\\
\frac{dI}{dt} &= -mI - (\bar c_{IS}S+\bar c_{II}I)I + \bar\beta SI - \bar\gamma I - \bar\mu I,
\end{aligned}
$$

with averaged coefficients $\bar a=(1-\nu^*)a_U+\nu^*a_V$, $\bar c_{SI}=(1-\nu^*)c_{SU}+\nu^*c_{SV}$, $\bar c_{IS}=(1-\nu^*)c_{US}+\nu^*c_{VS}$, $\bar c_{II}=(1-\nu^*)^2c_{UU}+(1-\nu^*)\nu^*(c_{UV}+c_{VU})+(\nu^*)^2c_{VV}$, $\bar\beta=(1-\nu^*)\beta_U+\nu^*\beta_V$, $\bar\gamma=(1-\nu^*)\gamma$ and $\bar\mu=(1-\nu^*)\mu_U+\nu^*\mu_V$. This has the same form as the primary-disease SIS submodel alone. A hyperbolic asymptotically stable equilibrium $(S^*,I^*)$ of the aggregated system yields, for $\varepsilon$ small enough, an asymptotically stable equilibrium of the full system near $(S^*,(1-\nu^*)I^*,\nu^*I^*)$.

## Expansion

The change of variables $(S,U,V)\mapsto(S,I,V)$ makes $S$ and $I$ slow (their right-hand sides carry the factor $\varepsilon$), leaving $V$ as the only fast variable; the fast dynamics is a classical frequency-dependent SIS model whose endemic fraction is $1-\delta/\lambda$. Approximate aggregation (a Tikhonov-type reduction) replaces the fast variable by its quasi-equilibrium, so the opportunistic disease enters the slow dynamics only through $\nu^*$: an endemic opportunistic infection averages the fertility, competition, transmission, recovery and mortality coefficients of the primary disease between the primary-only and coinfected classes, and coinfected hosts do not recover from the primary disease, which is why $\bar\gamma$ is scaled by $1-\nu^*$.

## Depends on

- [Solution of the SIS system](../../sis-epidemic-model/is-solution.md)

## Sources

- M. Marvá, E. Venturino, R. Bravo de la Parra, *A time scales approach to coinfection by opportunistic diseases*, arXiv:1403.3517 (2014). <https://doi.org/10.48550/arXiv.1403.3517> — Section 2 (primary and opportunistic submodels, full two-time-scale model and its reduction, equations for the fast equilibrium and the aggregated coefficients). Published version: Journal of Applied Mathematics 2015 (2015), 1–10, <https://doi.org/10.1155/2015/275485>; locators above refer to the arXiv version.
