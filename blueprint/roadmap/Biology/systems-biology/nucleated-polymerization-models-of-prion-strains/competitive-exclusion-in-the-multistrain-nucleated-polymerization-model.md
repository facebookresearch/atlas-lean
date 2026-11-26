# Competitive exclusion of prion strains in the nucleated polymerization model

**Model.** Let $V(t)$ be the amount of normal monomer, and for strains $i = 1, \dots, N$ let $U_i(t)$ be the number of aggregates and $P_i(t)$ their total mass (number of misfolded monomers). Monomers are produced at rate $\lambda$ and degraded at rate $\gamma$; strain-$i$ aggregates recruit monomers at rate $\tau_i$, break at rate $\beta_i$ per link, are cleared at rate $\mu_i$, and fragments below the nucleus size $x_i$ return their monomers to the normal pool. In the variables $W_i = P_i - x_i U_i$ the moment equations read

$$\frac{dV}{dt} = \lambda - \gamma V + \sum_{i=1}^N \big(-\tau_i V U_i + \beta_i x_i^2 U_i\big), \qquad \frac{dU_i}{dt} = \beta_i W_i - (\mu_i + \beta_i x_i) U_i, \qquad \frac{dW_i}{dt} = \tau_i V U_i - (\mu_i + \beta_i x_i) W_i,$$

equivalently $\dot U_i = \beta_i P_i - (\mu_i + 2\beta_i x_i) U_i$ and $\dot P_i = \tau_i V U_i - \mu_i P_i - \beta_i x_i^2 U_i$.

**Theorem 1.** Assume all parameters are positive. The system has a unique positive solution for every initial condition in $X = \{V, U_i, P_i - x_i U_i \ge 0\}$. Let

$$R_0^i = \frac{\lambda \beta_i \tau_i}{\gamma (\mu_i + \beta_i x_i)^2}$$

be distinct and $R_0 = \max_i R_0^i$.

1. If $R_0 \le 1$, the disease-free equilibrium $(\lambda/\gamma, 0, \dots, 0)$ is globally asymptotically stable on $X$.
2. If $R_0 > 1$ and strain 1 attains the maximum, there is a single-strain endemic equilibrium for every strain with $R_0^i > 1$, and the strain-1 equilibrium

$$V^* = \frac{(\mu_1 + \beta_1 x_1)^2}{\beta_1 \tau_1}, \quad U_1^* = \frac{\lambda \beta_1 \tau_1 - \gamma (\mu_1 + \beta_1 x_1)^2}{\mu_1 \tau_1 (\mu_1 + 2\beta_1 x_1)}, \quad P_1^* = \frac{\lambda \beta_1 \tau_1 - \gamma (\mu_1 + \beta_1 x_1)^2}{\mu_1 \beta_1 \tau_1},$$

with all other strains absent, is globally asymptotically stable on $\{U_1 > 0, P_1 > 0\} \cap X$.

So at most one strain propagates stably: the one with the largest $R_0^i$.

## Expansion

Strain $i$ can invade the monomer pool only if the steady monomer level $V$ exceeds its break-even level $(\mu_i + \beta_i x_i)^2/(\beta_i \tau_i)$, which is $\lambda/\gamma$ divided by $R_0^i$; the strain with the lowest break-even level pushes $V$ below every other strain's threshold, as in resource competition with one shared resource. Global stability is proved with Lyapunov functions: for the disease-free state $L = \tfrac12 (V - \lambda/\gamma)^2 + \sum_i b_i(\mu_i U_i/\beta_i + P_i)$ with constants $b_i > 0$ chosen so that $\dot L \le 0$ when all $R_0^i \le 1$, and a Volterra-type function in the variables $(V, U_i, W_i)$ for the endemic state. The paper's extension in which templating proceeds through a subunit species breaks this exclusion.

## Sources

- P. Lemarre, L. Pujo-Menjouet, S. S. Sindi, "Generalizing a mathematical model of prion aggregation allows strain coexistence and co-stability by including a novel misfolded species", Journal of Mathematical Biology 78 (2019) 465–495, Section 2, System (6), Theorem 1 and Appendix A, <https://doi.org/10.1007/s00285-018-1280-4> (PMC6399074).
