# Threshold dynamics of the hypnozoite superinfection model

**Model.** Couple the [within-host hypnozoite and MOB model](generating-function-of-hypnozoite-burden-and-multiplicity-of-infection.md) to mosquito infection: with $I_M(t)$ the proportion of infected mosquitoes, $g$ the mosquito death rate, $\beta$ the mosquito biting rate, $p$ and $q$ the mosquito-to-human and human-to-mosquito transmission probabilities per bite, $P_M, P_H$ the mosquito and human population sizes, $a = (P_M/P_H)\beta p$ and $b = \beta q$,

$$\frac{dI_M}{dt} = -g I_M + b\,(1 - I_M)\,I_H(t),$$

where $I_H(t)$ is the prevalence of blood-stage infection in humans. For an initially infection-naive human population ($H_{0,0}(0) = 1$) this infinite-compartment system is equivalent to the integrodifferential equation

$$\frac{dI_M}{dt} = -g I_M + b(1 - I_M)\left(1 - \exp\left\{-a\int_0^t I_M(\tau)\,z(t-\tau)\,d\tau\right\}\right),$$

with $z(s)$ the probability that a single bite still causes blood-stage infection after time $s$. Let

$$\mathcal R = \frac{ab}{g}\int_0^\infty z(s)\,ds,$$

where $\int_0^\infty z$ is the expected cumulative duration of blood-stage infection (primary plus relapses) attributable to one infective bite.

**Theorem.** Equilibria of the integrodifferential equation are the solutions $I_M^* \in [0,1)$ of

$$\frac{g I_M^*}{b(1 - I_M^*)} = 1 - \exp\left\{-a I_M^* \int_0^\infty z(s)\,ds\right\}.$$

1. If $\mathcal R < 1$, the disease-free equilibrium $I_M^* = 0$ is uniformly asymptotically stable and no endemic equilibrium exists.
2. If $\mathcal R > 1$, there is exactly one endemic equilibrium $I_M^* > 0$, and it is uniformly asymptotically stable when $I_M^*$ exceeds an explicit lower bound depending on $b/(b+g)$ and $\mathcal R$.

## Depends on

- [Generating function of hypnozoite burden and multiplicity of infection](generating-function-of-hypnozoite-burden-and-multiplicity-of-infection.md)

## Expansion

The reduction uses the closed form of $I_H(t) = 1 - H(1,0,t)$ from the generating function, which depends on the mosquito history only through $\int_0^t I_M(\tau)z(t-\tau)\,d\tau$. On $[0,1)$ the left side of the equilibrium equation is increasing, convex and blows up at 1, while the right side is increasing and concave with value 0 at 0; a second intersection exists if and only if the slope of the right side at 0, $a\int z$, exceeds that of the left side, $g/b$, i.e. $\mathcal R > 1$. Stability follows from Brauer's criterion for Volterra integrodifferential equations, applied to the equation linearized about each equilibrium. The underlying stochastic model, a density-dependent Markov population process indexed by hypnozoite and MOB counts, converges to the deterministic system by a functional law of large numbers of Barbour and Luczak, with error of order $\log P_M/\sqrt{P_M}$ in the mosquito population size $P_M$.

## Sources

- S. Mehra, J. M. McCaw, P. G. Taylor, "Superinfection and the hypnozoite reservoir for Plasmodium vivax: a general framework", Journal of Mathematical Biology 88 (2024) 7, Eqs. (7)–(12), (21)–(28), Theorems 3.2 and 4.1, <https://doi.org/10.1007/s00285-023-02014-3>, PMCID PMC10692056.
