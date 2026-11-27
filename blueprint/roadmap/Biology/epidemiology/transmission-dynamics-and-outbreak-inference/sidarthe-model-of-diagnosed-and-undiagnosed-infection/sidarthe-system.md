# SIDARTHE model of diagnosed and undiagnosed infection

Partition a closed population into the fractions susceptible $S$, infected and undetected without symptoms $I$, diagnosed without severe symptoms $D$, undetected with symptoms (ailing) $A$, diagnosed with symptoms (recognized) $R$, life-threatened $T$, healed $H$ and extinct $E$. With strictly positive parameters, the SIDARTHE system is

$$\begin{aligned}
\dot S &= -S\big(\alpha I + \beta D + \gamma A + \delta R\big), &
\dot I &= S\big(\alpha I + \beta D + \gamma A + \delta R\big) - (\varepsilon + \zeta + \lambda) I,\\
\dot D &= \varepsilon I - (\eta + \rho) D, &
\dot A &= \zeta I - (\theta + \mu + \kappa) A,\\
\dot R &= \eta D + \theta A - (\nu + \xi) R, &
\dot T &= \mu A + \nu R - (\sigma + \tau) T,\\
\dot H &= \lambda I + \rho D + \kappa A + \xi R + \sigma T, &
\dot E &= \tau T .
\end{aligned}$$

Here $\alpha,\beta,\gamma,\delta$ are transmission rates from the four infectious classes, $\varepsilon$ and $\theta$ detection rates, $\zeta$ and $\eta$ rates of developing symptoms, $\mu$ and $\nu$ rates of becoming life-threatened, $\tau$ the mortality rate and $\lambda,\kappa,\xi,\rho,\sigma$ recovery rates. The system is positive: non-negative initial data give non-negative solutions for all $t \ge 0$. Summing the eight equations gives $\dot S + \dot I + \dot D + \dot A + \dot R + \dot T + \dot H + \dot E = 0$, so with initial data summing to $1$,

$$S(t) + I(t) + D(t) + A(t) + R(t) + T(t) + H(t) + E(t) = 1 \qquad \text{for all } t \ge 0 .$$

Every equilibrium has $\bar I = \bar D = \bar A = \bar R = \bar T = 0$ and $\bar S + \bar H + \bar E = 1$.

## Remarks

The model separates detection from disease severity, so a diagnosed case and an undiagnosed case of the same clinical stage differ only in their transmission rate: that is what lets testing policy ($\varepsilon$, $\theta$) and distancing policy ($\alpha,\beta,\gamma,\delta$) act on different parameters of the same system. Mass conservation is immediate because every term appears once with each sign, the deceased being counted in $E$; it also shows $H$ and $E$ are cumulative and determined by the other states. No latency class appears, which encodes the assumption that an infected individual transmits before symptoms, and no reinfection term appears, which is the assumption of lasting immunity on the timescale modelled.

## Sources

- Giordano G, Blanchini F, Bruno R, et al. Modelling the COVID-19 epidemic and implementation of population-wide interventions in Italy. *Nature Medicine* 26:855-860 (2020), Methods, equations (1)-(8). DOI <https://doi.org/10.1038/s41591-020-0883-7>. PMCID PMC7175834.
