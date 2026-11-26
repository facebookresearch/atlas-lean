# Reproduction number and final size of the age-dependent immuno-epidemic SIR model

**General model.** Let $S(x,t), I(x,t), R(x,t), D(x,t)$ be the densities of susceptible, infected, recovered and dead individuals of age $x \ge 0$ at time $t$ (ages do not advance on the epidemic time scale). With susceptibility $\alpha(x) > 0$, infectivity (total viral load) $W(y) \ge 0$ of infected individuals of age $y$, and incidence $J(x,t) = \alpha(x)S(x,t)\int_0^\infty W(y)I(y,t)\,dy$,

$$\partial_t S = -J, \qquad \partial_t I = J - \int_0^t \big(r(x,t-\eta) + d(x,t-\eta)\big)J(x,\eta)\,d\eta, \qquad \partial_t R = \int_0^t r(x,t-\eta)J(x,\eta)\,d\eta, \qquad \partial_t D = \int_0^t d(x,t-\eta)J(x,\eta)\,d\eta,$$

with recovery and death kernels $r, d \ge 0$ satisfying $\int_\eta^{t_0}(r+d)(x, t-\eta)\,dt \le 1$. On $[0,Q]\times[0,T_f]$ this system has a unique nonnegative solution (a contraction mapping argument in a weighted sup-metric).

**Reduction.** If recovery and death act at constant rates $\gamma(x)$, $\delta(x)$ during the disease duration $\tau(x)$ and terms of order $(\gamma+\delta)^2$ are neglected, the model becomes the age-structured SIR system

$$\partial_t S = -\alpha(x)S\!\int_0^\infty\! W(y)I(y,t)\,dy, \qquad \partial_t I = \alpha(x)S\!\int_0^\infty\! W(y)I(y,t)\,dy - (\gamma(x)+\delta(x))I, \qquad \partial_t R = \gamma(x) I, \quad \partial_t D = \delta(x) I.$$

**Theorem.** For this system with initial susceptible density $S_0(x)$, let

$$\mathcal R_0 = \int_0^\infty \frac{W(y)\,\alpha(y)\,S_0(y)}{\gamma(y) + \delta(y)}\,dy .$$

1. If $\mathcal R_0 < 1$, the disease-free equilibrium $(S_0, 0, 0, 0)$ is locally asymptotically stable; if $\mathcal R_0 > 1$ it is unstable.
2. (Final size) If $\mathcal R_0 > 1$, the limiting susceptible density is

$$S_f(x) = S_0(x)\,e^{-A^*\alpha(x)},$$

where $A^* > 0$ is the unique positive root of

$$A = \int_0^\infty \frac{W(y)\,S_0(y)\big(1 - e^{-A\alpha(y)}\big)}{\gamma(y) + \delta(y)}\,dy .$$

With $S_0 \equiv N$, constant rates and $W$ replaced by a Dirac mass at the infected individual's own age, $\mathcal R_0 = \beta N/(\gamma_0 + \delta_0)$, the classical SIR value.

## Expansion

Because transmission is separable (susceptibility of the recipient's age times infectivity of the infector's age), the linearization at the disease-free state has a rank-one structure: exponential solutions $e^{\lambda t}$ exist exactly when $G(\lambda) = \int_0^\infty W\alpha S_0/(\lambda + \gamma + \delta)\,dy = 1$. $G$ is decreasing on the real line with $G(0) = \mathcal R_0$ and $G(\lambda) \to 0$, so $\mathcal R_0 > 1$ yields a positive real root; if $\mathcal R_0 < 1$, then $|G(\lambda)| \le G(\operatorname{Re}\lambda) \le \mathcal R_0 < 1$ for $\operatorname{Re}\lambda \ge 0$, excluding unstable roots. For the final size, dividing the $S$ equation by $S$ and integrating gives $\ln(S_f/S_0) = -\alpha(x)\int W(y)\int_0^\infty I(y,t)\,dt\,dy$, while adding the $S$ and $I$ equations gives $S_f - S_0 = -(\gamma+\delta)\int_0^\infty I\,dt$; combining them yields the fixed-point equation for $A$. The function $F(A) = A - \int W S_0(1-e^{-A\alpha})/(\gamma+\delta)$ has $F(0) = 0$, $F'(0) = 1 - \mathcal R_0 < 0$, strictly increasing $F'$ and $F \to \infty$, so the positive root is unique.

## Sources

- S. Ghosh, V. Volpert, M. Banerjee, "An age-dependent immuno-epidemiological model with distributed recovery and death rates", Journal of Mathematical Biology (2023), Eqs. (3.2)–(3.4), (4.1)–(4.13), Lemmas 1–4, Theorems 1 and 3, <https://doi.org/10.1007/s00285-022-01855-8>, PMCID PMC9838470.
