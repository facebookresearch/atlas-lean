# Coevolutionary singular strategies of resistance and virulence

**Ecological model.** Susceptible hosts $S$ and infected hosts $I$ (which neither reproduce nor recover), with total density $N = S + I$ and density-dependent mortality $m(N) = m_0 + m_1 N$, obey

$$\dot S = b(x_1)S - \beta(x_1 - x_2)SI - m(N)S, \qquad \dot I = \beta(x_1 - x_2)SI - \alpha(x_2)I - m(N)I,$$

where $x_1$ is host resistance, $x_2$ pathogen virulence, $b' < 0$ (resistance is costly), $\alpha' > 0$ (virulence kills the host) and $\beta$ is decreasing in $x_1 - x_2$ (an asymmetric interaction). Infection can spread iff

$$\mathcal R_0 = \frac{\beta(x_1 - x_2)\,(b(x_1) - m_0)}{(b(x_1) + \alpha(x_2))\,m_1} > 1,$$

and then the endemic equilibrium $(S^*, I^*)$ is globally asymptotically stable in the open positive quadrant.

**Invasion fitness and canonical equation.** A rare mutant host $y_1$ or pathogen $y_2$ in the resident community at $(S^*, I^*)$ has invasion fitness

$$f_1(y_1; x_1, x_2) = b(y_1) - \beta(y_1 - x_2)I^* - m(N^*), \qquad f_2(y_2; x_1, x_2) = \beta(x_1 - y_2)S^* - \alpha(y_2) - m(N^*),$$

and successful invasion leads to trait substitution. With small rare mutations (probabilities $\mu_i$, variances $\sigma_i^2$),

$$\frac{dx_1}{d\tau} = \tfrac12\mu_1\sigma_1^2 S^*\,g_1, \qquad \frac{dx_2}{d\tau} = \tfrac12\mu_2\sigma_2^2 I^*\,g_2, \qquad g_i = \frac{\partial f_i}{\partial y_i}\Big|_{y_i = x_i}.$$

**Theorem.** Let $(x_1^*, x_2^*)$ be a singular strategy ($g_1 = g_2 = 0$) with $\mathcal R_0 > 1$, and let $J$ be the Jacobian of the canonical equation there.
1. (Continuously stable strategy) If $\det J > 0$, $\operatorname{tr} J < 0$ and both $\partial^2 f_1/\partial y_1^2 = b''(x_1^*) - \beta''I^* < 0$ and $\partial^2 f_2/\partial y_2^2 = \beta''S^* - \alpha''(x_2^*) < 0$, the singular strategy is convergence stable and evolutionarily stable: coevolution ends in one monomorphic host and one monomorphic pathogen.
2. (Branching) If the singular strategy is convergence stable but the host (resp. pathogen) fitness is locally convex in its own mutant trait, with the corresponding mutual-invasibility inequality, and the other player's fitness is locally concave in its own trait ($\beta''S^* - \alpha''(x_2^*) < 0$ for host branching, $b''(x_1^*) - \beta''I^* < 0$ for pathogen branching), evolutionary branching of host resistance (resp. pathogen virulence) occurs, leading to dimorphic hosts (resp. pathogens).
3. (Cycles) When $\det J > 0$ and $\operatorname{tr} J$ changes sign, the singular strategy loses convergence stability through a Hopf bifurcation of the canonical equation, and resistance and virulence then cycle on the evolutionary time scale (exhibited numerically for strong virulence trade-offs).
4. (After host branching) For two host strains and one pathogen, the endemic equilibrium is again globally stable, and a convergence-stable singular strategy satisfying the corresponding second-derivative conditions is continuously stable.

## Depends on

- [Convergence stability](../../../classification-of-adaptive-dynamics-singular-str/convergence-stable-iff-and-gradient.md)
- [Evolutionary branching point](../../../classification-of-adaptive-dynamics-singular-str/branching-point.md)

## Proof depends on

- [LaSalle's invariance principle](../../../../../Dynamics/smooth-dynamics/lasalle-s-invariance-principle/lasalle.md)

## Expansion

Global stability of $(S^*, I^*)$ uses $V = S - S^* - S^*\ln(S/S^*) + I - I^* - I^*\ln(I/I^*)$, for which $\dot V = -m_1\big((S - S^*) + (I - I^*)\big)^2 \le 0$, and LaSalle's principle. The invasion fitness is the per-capita growth rate of a mutant at low density in the resident environment fixed by $(S^*, I^*)$. Convergence stability is linear stability of the canonical equation, whose Jacobian is built from second derivatives of $b$, $\alpha$ and $\beta$ weighted by $S^*$, $I^*$ and the mutational speeds; evolutionary stability requires each player's fitness to have a local maximum at its own resident trait. Accelerating costs (convex $b$, concave $\alpha$ in the cost sense) favour a continuously stable outcome, while decelerating costs together with a sharply asymmetric transmission function favour branching. After host branching, two host strains coexist with one pathogen, and after pathogen branching two pathogen strains coexist with one host.

## Sources

- Y. Yang, C. Ma, J. Zu, "Coevolutionary dynamics of host-pathogen interaction with density-dependent mortality", Journal of Mathematical Biology 85 (2022) 15, models (1)–(2), Eqs. (3)–(11), Proposition 1, invasion fitnesses $f_1, f_2$, canonical equation, Proposition 3 and Theorems 1–3, <https://doi.org/10.1007/s00285-022-01782-8>, PMCID PMC9309463.
