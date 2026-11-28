# Delay-equation reduction of juvenile–adult predator–prey models

**Age-structured model.** Prey $R(t)$ grow logistically. Predators are structured by age $a$ into juveniles ($a < \tau$, the maturation age) and adults ($a \ge \tau$), with constant per-capita death rates $\mu_1$ (juveniles) and $\mu_2$ (adults). Each class follows a Lotka–Sharpe (McKendrick–von Foerster) equation $\partial_tp + \partial_ap = -\mu p$, and newborns are produced at the boundary $a = 0$ by adults at rate $b_2h(R,P_2)$, where $h$ is a nondecreasing function of food intake. Integrating the PDE over the two age classes, with $P_1(t) = \int_0^\tau p\,da$ and $P_2(t) = \int_\tau^\infty p\,da$, gives for $t \ge \tau$ the closed delay system

$$\begin{aligned} R'(t) &= r\Bigl(1 - \frac{R(t)}{K}\Bigr)R(t) - g(t)\,\delta\bigl(P_1(t),P_2(t)\bigr),\\ P_1'(t) &= -\mu_1P_1(t) + b_2h(t)P_2(t) - b_2h(t-\tau)\,e^{-\mu_1\tau}P_2(t-\tau),\\ P_2'(t) &= b_2h(t-\tau)\,e^{-\mu_1\tau}P_2(t-\tau) - \mu_2P_2(t), \end{aligned}$$

where $h(t) = h(R(t),P_2(t))$, $g$ is the functional response, and $e^{-\mu_1\tau}$ is the probability of surviving the juvenile stage. If fertility has a peak at the age of maturity ($b_{p,3}>0$ in the source's notation), the same procedure gives a neutral delay system in $P_2'(t-\tau)$; juvenile reproduction instead adds terms in $P_1(t-\tau)$. For $t < \tau$, the maturation term is replaced by the contribution $p_1^0(\tau-t)e^{-\mu_1t}$ of the initial juvenile age distribution $p_1^0$.

**Theorem.**

1. (Physically admissible histories.) Let $\mathcal K$ be the cone of $(R, P_1, P_2) \in C[0,\tau]^3$ with $R(0) \ge 0$, $P_2(0) \ge 0$, $t \mapsto P_2(t)e^{\mu_2t}$ nondecreasing on $[0,\tau]$, and $P_1$ determined from $(R, P_2)$ by the variation-of-constants formula

$$P_1(t) = \bigl(P_1(0) + P_2(0)\bigr)e^{-\mu_1t} - P_2(t) + \int_0^t\bigl(b_2h(s) - \mu_2\bigr)P_2(s)\,e^{\mu_1(s-t)}ds + \mu_1\int_0^tP_2(s)\,e^{\mu_1(s-t)}ds,$$

with $P_1(0) = P_2(\tau)e^{\mu_1\tau} - P_2(0) - (\mu_1 - \mu_2)\int_0^\tau P_2(t)e^{\mu_1t}dt$. A history on $[0,\tau]$ comes from a nonnegative initial juvenile age distribution $p_1^0 \ge 0$ if and only if it lies in $\mathcal K$. Such histories generate nonnegative solutions, whereas arbitrary nonnegative initial functions of a delay equation may produce negative densities.

2. (Delay-induced stability switches.) Assume that predation is due to adults only, $\delta(P_1,P_2) = \delta(P_2)$, that the functional response is $g(t) = g(R(t),P_2(t))$, and that there is a unique coexistence equilibrium $E_C = (R^*,P_1^*,P_2^*)$. Set

$$\beta = \frac{2r}{K}R^* + g_R(R^*,P_2^*)\,\delta(P_2^*) - r, \qquad \gamma = b_2h(R^*,P_2^*) + b_2h_{P_2}(R^*,P_2^*)\,P_2^*,$$

$$\varepsilon = b_2h_R(R^*,P_2^*)\,P_2^*\big(g_{P_2}(R^*,P_2^*)\,\delta(P_2^*) + g(R^*,P_2^*)\,\delta'(P_2^*)\big),$$

$$M(\tau) = \beta^2 + \mu_2^2 - e^{-2\mu_1\tau}\gamma^2, \qquad N(\tau) = e^{-2\mu_1\tau}(\gamma\beta - \varepsilon)^2 - \mu_2^2\beta^2,$$

all evaluated at the $\tau$-dependent point $E_C$. Then $P_1$ decouples (giving the root $\lambda = -\mu_1$), and linearizing at $E_C$ gives a characteristic equation $P(\lambda;\tau) + Q(\lambda;\tau)e^{-\lambda\tau} = 0$ with $P(\lambda;\tau) = \lambda^2 + (\beta + \mu_2)\lambda + \mu_2\beta$ and $Q(\lambda;\tau) = -e^{-\mu_1\tau}(\gamma\lambda + \gamma\beta - \varepsilon)$, whose coefficients depend on $\tau$ through $e^{-\mu_1\tau}$ and through $E_C$ itself. Purely imaginary roots $\lambda = iy$ require $F(y;\tau) = |P(iy;\tau)|^2 - |Q(iy;\tau)|^2 = y^4 + M(\tau)y^2 - N(\tau) = 0$. If moreover $\beta(\gamma - \mu_2e^{\mu_1\tau}) \ne \varepsilon$ (so that $\lambda = 0$ is not a root), then by the Beretta–Kuang criterion stability switches of $E_C$ can occur only for delays in the set where $M(\tau) \ge 0$ and $N(\tau) > 0$, or where $M(\tau) < 0$ and $N(\tau) \ge -M(\tau)^2/4$. Outside this set, increasing $\tau$ produces no switch.

So delay predator–prey models with a correct biological derivation carry the juvenile survival factor $e^{-\mu_1\tau}$ and a constrained history. Several delay models in the literature, including the Gourley–Kuang model, are recovered as special cases, while others lack these features.

## Expansion

Along characteristics $t - a = \text{const}$, the age density decays as $e^{-\mu_1a}$, so newborns at time $t - \tau$ reach maturity at time $t$ with density $b_2h(t-\tau)P_2(t-\tau)e^{-\mu_1\tau}$. Integrating $\partial_tp + \partial_ap = -\mu p$ over $[0,\tau)$ and $[\tau,\infty)$ turns boundary fluxes at $a = 0$ and $a = \tau$ into the source and maturation terms. For $t < \tau$, the maturation flux is $p_1^0(\tau - t)e^{-\mu_1t} \ge 0$. Requiring this flux to be nonnegative and expressing it through $P_2$ gives the monotonicity of $P_2e^{\mu_2t}$ and the formula for $P_1$, which characterizes $\mathcal K$. The switching criterion is the Beretta–Kuang geometric method for characteristic equations with delay-dependent coefficients.

## Sources

- Marcel Mohr, Maria Vittoria Barbarossa, Christina Kuttler, "Predator-Prey Interactions, Age Structures and Delay Equations", arXiv (2013). Section "Model derivation" (Lotka–Sharpe system and reduction to delay equations), Section "Analytical Results" (positivity proposition with the cone $\mathcal K$, linearized stability, stability-switch theorem). <https://doi.org/10.48550/arXiv.1308.2532>. Published version: Mathematical Modelling of Natural Phenomena 9(1) (2014), 92–107, <https://doi.org/10.1051/mmnp/20149107>; locators above refer to the arXiv version.
