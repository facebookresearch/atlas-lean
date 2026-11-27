# Extinction conditions for SIS epidemics with Brownian and Poisson perturbations

**Model.** Let $S,I$ be population fractions ($S+I=1$), with transmission rate $\beta$, recovery rate $\lambda$ and birth and death rate $\mu$. Contacts fluctuate through a Brownian motion $W$ with intensity $\sigma$, and sudden **anomalies** (for example quarantine events) arrive through an independent Poisson random measure $N(dt,dy)$ with finite intensity measure $\nu$ ($\nu(\mathbb R)<\infty$), with continuously differentiable jump effect $h(y)\in(-1,1)$. The stochastic SIS model is

$$dS=\bigl(-\beta SI-\mu S+\mu+\lambda I\bigr)dt-\sigma SI\,dW+\int_{\mathbb R}h(y)\,S(t^-)I(t^-)\,N(dt,dy),$$

$$dI=\bigl(\beta SI-(\lambda+\mu)I\bigr)dt+\sigma SI\,dW-\int_{\mathbb R}h(y)\,S(t^-)I(t^-)\,N(dt,dy).$$

Without noise, the disease-free state $(1,0)$ is globally stable iff $\beta\le\mu+\lambda$.

**Theorem.**

1. (Well-posedness) Starting in the open simplex, the solution stays in the simplex for all finite times almost surely.
2. (Extinction) If $\int_{\mathbb R}h(y)\,\nu(dy)<0$ and $\beta<\mu+\lambda+\int_{\mathbb R}h(y)\,\nu(dy)$, then $(S,I)\to(1,0)$ almost surely. If $h\ge0$ and $\beta<\mu+\lambda+\varphi\int_{\mathbb R}h(y)\,\nu(dy)$ for some $\varphi\in(0,1)$, the same conclusion holds.

Positive quarantine jumps thus effectively add to the recovery rate, lowering the transmission rate at which the disease can persist.

## Depends on

- [SIS epidemic model](../../sis-epidemic-model/README.md)

## Expansion

Since $S+I=1$, the model reduces to a one-dimensional jump-diffusion for $S$ on $(0,1)$ with drift $\alpha(S)$, diffusion coefficient $\sigma S(1-S)$ and multiplicative jumps $h(y)S(1-S)$. Invariance of the simplex follows because the coefficients vanish at the boundary and jumps of relative size $|h|<1$ cannot leave $[0,1]$. The hitting time of $[1-\epsilon,1]$ has finite expectation, and a stability criterion of Gihman–Skorohod type for jump-diffusions (stated for compensated Poisson measures, applicable here since $\nu$ is finite so the compensator can be absorbed into the drift) shows that $1-S=I$ tends to zero when the averaged growth rate of $\ln I$, namely $\beta-\mu-\lambda$ corrected by the jump term, is negative.

## Sources

- Andrew Vlasic, Troy Day, "Modeling stochastic anomalies in an SIS system", Stochastic Analysis and Applications 35(1) (2017), 27–39, <https://doi.org/10.1080/07362994.2016.1216320>. Preprint: Andrew Vlasic, "Modeling Stochastic Anomalies in an SIS and SIRS System", arXiv:1205.5264 (2012), <https://doi.org/10.48550/arXiv.1205.5264>; locators refer to this version: Section 1 (model (3), Proposition 1.1) and Section 2 (Claim 2.1, Theorem 2.1, Corollary 2.1).
