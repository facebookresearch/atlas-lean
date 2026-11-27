# Observability and identifiability of the SIS model from primo-infected prevalence

Consider the normalized SIS model with births and deaths at the same known rate $\mu > 0$, transmission rate $\beta$ and recovery rate $\gamma$, total population $S + I = 1$, in which infected individuals are counted by infection number. Its first-infection subsystem, together with the total, is

$$ \dot S = \mu - \beta S I - \mu S + \gamma I, \quad \dot I = \beta S I - (\mu+\gamma) I, \quad \dot S_1 = \mu - \beta S_1 I - \mu S_1, \quad \dot I_1 = \beta S_1 I - (\mu+\gamma) I_1, $$

where $S_1$ are susceptibles never infected and $I_1$ are individuals in their first (primo-) infection. Two outputs may be measured, with the same unknown reporting fraction $\alpha \in (0,1]$:

$$ y = \alpha I, \qquad y_1 = \alpha I_1. $$

The unknown parameters are $(\alpha, \beta, \gamma)$.

**Theorem.** With the single output $y$, the system is neither observable nor identifiable. With both outputs $y$ and $y_1$, it is both observable and identifiable.

**Equilibrium version.** Let $\mathcal R_0 = \beta / (\gamma + \mu) > 1$ and suppose the endemic limits $I^* = 1 - 1/\mathcal R_0$ and $I_1^*$ are measured exactly ($\alpha = 1$). Writing $\theta = I_1^* / I^*$ for the primo-infected share of the infected population, the equilibrium relations $I_1^* = \mathcal R_0 S_1^* I^*$ and $S_1^* = \mu / (\beta I^* + \mu)$ give

$$ \mathcal R_0 = \frac{1}{1 - I^*}, \qquad \beta = \frac{\mu \mathcal R_0}{\mathcal R_0 - 1}\left(\frac{\mathcal R_0}{\theta} - 1\right), \qquad \gamma = \frac{\mu \mathcal R_0}{\mathcal R_0 - 1}\left(\frac{1}{\theta} - 1\right), $$

so both rates are recovered from the two prevalences, while $I^*$ alone determines only $\mathcal R_0$. The share $\theta$ is also the fraction of never-infected individuals among susceptibles.

## Proof depends on

- [Geometric law of reinfection counts at the SEIRS endemic equilibrium](geometric-law-of-reinfection-counts-at-the-seirs-endemic-equilibrium.md)

## Expansion

With $y$ alone, $S + I = 1$ reduces the dynamics to the logistic equation $\dot y = (\beta - \mu - \gamma - (\beta/\alpha) y)\, y$. Differentiating $\dot y / y$ identifies $\beta / \alpha$ and $\beta - \gamma$, and nothing else: any $(\alpha, \beta, \gamma)$ with the same two combinations yields the same output, and $I = y/\alpha$ cannot be reconstructed. The second output adds the equation $\dot y_1 = w y - (\mu + \gamma) y_1$ with $w = \beta S_1$, and the $S_1$ equation gives $\dot w = \beta\mu - (\beta/\alpha) w y - \mu w$, in which $\beta/\alpha$ is already known from $y$. Eliminating $w$ yields an expression for $\ddot y_1$ that is affine in the unknowns $\beta$ and $\gamma$ with coefficients built from $y$, $y_1$ and their derivatives; generically it can be solved for them, after which $\alpha$ and the full state follow.

In the source, the equilibrium formulas are printed as $\beta = \frac{\mu}{\mathcal R_0 - 1}\left(\frac{\mathcal R_0^2}{\theta} - 1\right)$ and $\gamma = \frac{\mu}{\mathcal R_0 - 1}\left(\frac{\mathcal R_0}{\theta} - 1\right)$. These do not satisfy the model's equilibrium equations: for $\mu = \gamma = 1$, $\beta = 4$ one has $\mathcal R_0 = 2$ and $\theta = 2/3$, and the printed formulas return $\beta = 5$, $\gamma = 2$. The forms stated above are derived from the model and return $\beta = 4$, $\gamma = 1$.

## Sources

- M. Fang and P.-A. Bliman, *Modelling, Analysis, Observability and Identifiability of Epidemic Dynamics with Reinfections*, arXiv:2201.10157 (2022), Section "Observability and identifiability of a simplified SIS model", Theorems 5 and 6. <https://doi.org/10.48550/arXiv.2201.10157> Published version: 2022 European Control Conference (ECC) (2022) 278–283, <https://doi.org/10.23919/ecc55457.2022.9838334>.
