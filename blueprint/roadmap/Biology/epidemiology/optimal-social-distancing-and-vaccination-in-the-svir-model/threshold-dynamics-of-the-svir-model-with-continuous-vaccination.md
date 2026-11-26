# Threshold dynamics of the SVIR model with continuous vaccination

Let $S, V, I, R$ be the susceptible, vaccinated, infected and recovered fractions of a population of constant size $1$. Vaccination happens at rate $\alpha \ge 0$; immunity after vaccination develops at rate $\gamma_1$, and vaccinated individuals can still be infected, at rate $\beta_1$, before then. Births and deaths occur at rate $\mu$:

$$
\begin{aligned}
S' &= -\beta S I - \alpha S + \mu - \mu S, \\
V' &= \alpha S - \beta_1 V I - \gamma_1 V - \mu V, \\
I' &= \beta S I + \beta_1 V I - \gamma I - \mu I, \\
R' &= \gamma_1 V + \gamma I - \mu R,
\end{aligned}
$$

with $\beta, \beta_1, \gamma, \gamma_1, \mu > 0$. The control reproduction number is

$$
R_0^C = \frac{\mu\beta}{(\mu + \alpha)(\mu + \gamma)} + \frac{\alpha\mu\beta_1}{(\mu + \gamma_1)(\mu + \alpha)(\mu + \gamma)}.
$$

**Theorem.** The disease-free equilibrium $E_0$ always exists. It is globally asymptotically stable if $R_0^C \le 1$, and unstable if $R_0^C > 1$. A positive (endemic) equilibrium $E_+$ exists if and only if $R_0^C > 1$; it is then unique and globally asymptotically stable on the feasible region minus the disease-free invariant set.

## Depends on

- [Basic reproduction number from the next-generation matrix](../../epidemiology/next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

The two terms of $R_0^C$ count secondary infections caused through susceptibles and through vaccinated individuals not yet immune, each weighted by the equilibrium share of that class ($\mu/(\mu+\alpha)$ and $\alpha\mu/((\mu+\alpha)(\mu+\gamma_1))$) and by the infectious period $1/(\mu+\gamma)$. Local stability follows from the next-generation construction, with the new-infection terms $\beta S I$ and $\beta_1 V I$ evaluated at $E_0 = (\mu/(\mu+\alpha), \alpha\mu/((\mu+\alpha)(\mu+\gamma_1)), 0)$. The global statements are due to Liu, Takeuchi and Iwami, whose SVIR analysis this model reproduces when vaccination is constant.

## Sources

- Alessandro Ramponi, M. Elisabetta Tessitore, "Optimal Social and Vaccination Control in the SVIR Epidemic Model", arXiv (2023). Section 2, Theorem 1 and Theorem 2 (results of Liu, Takeuchi and Iwami recalled there). <https://doi.org/10.48550/arXiv.2311.15718>
