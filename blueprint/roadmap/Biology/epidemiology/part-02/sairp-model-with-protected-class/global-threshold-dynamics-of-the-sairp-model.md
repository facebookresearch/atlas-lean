# Global threshold dynamics of the SAIRP model

Let $S, A, I, R, P$ be susceptible, asymptomatic infected, active (symptomatic) infected, removed and protected individuals, $N = S + A + I + R + P$. With recruitment $\Lambda > 0$, natural death rate $\mu > 0$, transmission rate $\beta > 0$, relative infectiousness of asymptomatics $\theta \in [0,1]$, protected fraction $p \in [0,1)$ entering protection at rate $\phi$, loss of protection at rate $\omega$, progression rate $\nu$ from $A$ to $I$ and removal rate $\delta$:

$$
\begin{aligned}
\dot S &= \Lambda - \beta(1-p)\frac{\theta A + I}{N} S - \phi p S + \omega P - \mu S, &
\dot A &= \beta(1-p)\frac{\theta A + I}{N} S - (\nu + \mu) A,\\
\dot I &= \nu A - (\delta + \mu) I, &
\dot R &= \delta I - \mu R, \qquad \dot P = \phi p S - (\omega + \mu) P .
\end{aligned}
$$

**Theorem.**

1. (Well-posedness) For every initial condition in $\Omega = \{x \in \mathbb{R}^5_{\ge 0} : 0 < N \le \Lambda/\mu\}$ there is a unique global non-negative solution, and $\Omega$ is positively invariant.

2. (Equilibria) The disease-free equilibrium is

    $$\Sigma_0 = \Big(\frac{\Lambda(\omega + \mu)}{\mu(p\phi + \mu + \omega)},\,0,\,0,\,0,\,\frac{\phi p\Lambda}{\mu(p\phi + \mu + \omega)}\Big),$$

    and the basic reproduction number is

    $$R_0 = \frac{\beta(1-p)\,(\delta\theta + \mu\theta + \nu)\,(\omega + \mu)}{(\delta + \mu)(\nu + \mu)(p\phi + \mu + \omega)} .$$

    A unique endemic equilibrium $\Sigma_+$ exists iff $R_0 > 1$.

3. (Global stability) If $R_0 < 1$, $\Sigma_0$ is globally asymptotically stable in $\Omega$. If $R_0 > 1$, $\Sigma_+$ is globally asymptotically stable on the invariant set $\Gamma = \{x \in \mathbb{R}^5_{\ge 0} : N = \Lambda/\mu\}$ (away from the disease-free boundary).

4. (Waves under switching) Let $\alpha_0, \alpha_+$ be parameter vectors with $R_0(\alpha_0) < 1 < R_0(\alpha_+)$, and alternate them on successive time intervals $[T_i, T_{i+1})$, and assume that each switch is made once the state has entered the basin of the next target equilibrium. Then the piecewise-defined solution alternates between neighbourhoods of $\Sigma_0$ and $\Sigma_+$. The switches back to $\alpha_0$ can always be made, since for $R_0(\alpha_0) < 1$ the equilibrium $\Sigma_0$ attracts all of $\Omega$ (item 3); for the switches to $\alpha_+$ the assumption is not removed, since item 3 gives attraction to $\Sigma_+$ only on $\Gamma$.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

At $\Sigma_0$ the susceptible fraction is $S_0/N_0 = (\omega + \mu)/(p\phi + \mu + \omega)$. An asymptomatic case infects at rate $\theta\beta(1-p)S_0/N_0$ for mean time $1/(\nu+\mu)$, and with probability $\nu/(\nu + \mu)$ becomes symptomatic, infecting at rate $\beta(1-p)S_0/N_0$ for mean time $1/(\delta+\mu)$; adding the two contributions gives $R_0$. Global stability of $\Sigma_0$ uses the Lyapunov functional

$$L = S - S_0 - S_0\ln\frac{S}{S_0} + A + \zeta I + \xi\Big(P - P_0 - P_0\ln\frac{P}{P_0}\Big) + \chi\Big(N - N_0 - N_0\ln\frac{N}{N_0}\Big)$$

with $\xi = \omega P_0/(\phi p S_0)$, a positive $\zeta$ fixed by $R_0 < 1$, and $\chi$ large, combined with $2 - x - 1/x \le 0$ and Young's inequality. Item 4 explains how alternating lockdown and relaxation (parameters with $R_0$ below and above one) produces pseudo-periodic epidemic waves even though the autonomous model has no periodic orbits.

## Sources

- C. J. Silva, G. Cantin, C. Cruz, R. Fonseca-Pinto, R. Passadouro, E. Soares dos Santos, D. F. M. Torres, "Complex network model for COVID-19: human behavior, pseudo-periodic solutions and multiple epidemic waves", Journal of Mathematical Analysis and Applications 514(2) (2022) 125171, system (1), Eqs. (4)–(8), (12), (16), Theorem 1, Proposition 1, Theorems 2–5, <https://doi.org/10.1016/j.jmaa.2021.125171>, PMCID PMC7983391.
