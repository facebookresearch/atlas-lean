# Gaussian self-similar reduction of the heterogeneous SIR model

Let susceptibles be distributed over a risk trait $a \in \mathbb{R}_+$ with density $S(t, a)$, let $I(t)$, $R(t)$ be the infected and removed counts, $N$ the population size, $\beta(a) \ge 0$ the trait-dependent transmission rate and $\gamma > 0$ the removal rate. If each susceptible's trait follows the diffusion $da_t = (\mu_{\mathrm{ep}} + \mu_b)\,dt + \sigma\,dW_t$ reflected at the boundary, where $\mu_{\mathrm{ep}}$ is the drift induced by epidemic depletion, the model is

$$\partial_t S = -\frac{\beta(a) I S}{N} - \partial_a(\mu_b S) + \frac12\partial_a^2(\sigma^2 S), \qquad \frac{dI}{dt} = I\Big(\frac1N\int_{\mathbb{R}_+}\beta(a)S(t,a)\,da - \gamma\Big), \qquad \frac{dR}{dt} = \gamma I,$$

with $\partial_a S = 0$ on the boundary and $\mu_b - \tfrac12\partial_a\sigma^2 = 0$ there.

**Statement.** Assume $\sigma^2/2 = D(t)$ does not depend on $a$, $\beta(a) = \beta_0 + \beta_1 a^2$ with $\beta_0, \beta_1 \ge 0$, background drift $\mu_b(t, a) = -\mu_0(t)\,a$, and a truncated-Gaussian initial profile. Then the PDE system admits the exact self-similar solution

$$S(t, a) = \frac{S(t)}{\lambda(t)}\,\varphi\!\Big(\frac{a}{\lambda(t)}\Big), \qquad \varphi(A) = \sqrt{\tfrac{2}{\pi}}\,e^{-A^2/2}\ (A \ge 0),$$

where $(S, \lambda, I, R)$ solve the ODE system

$$\frac{dS}{dt} = -\frac{S I(\beta_0 + \beta_1\lambda^2)}{N}, \qquad \frac{d\lambda}{dt} = -\frac{I\beta_1\lambda^3}{N} - \mu_0\lambda + \frac{D}{\lambda}, \qquad \frac{dI}{dt} = \frac{S I(\beta_0 + \beta_1\lambda^2)}{N} - \gamma I, \qquad \frac{dR}{dt} = \gamma I.$$

The population-average transmission rate $\bar\beta(t) = \beta_0 + \beta_1\lambda(t)^2$ then satisfies

$$\frac{d\bar\beta}{dt} = -\frac{2I}{N}(\bar\beta - \beta_0)^2 - 2\mu_0(\bar\beta - \beta_0) + 2D\beta_1,$$

so $(S, \bar\beta, I, R)$ is an SIR model whose transmission rate is depleted by the epidemic (infection removes high-risk susceptibles first), relaxed by the background drift and replenished by social diffusion. With $\beta_1 = 0$ or $\bar\beta(0) = \beta_0$ and $D = 0$ it is the classical SIR model.

## Depends on

- [Kermack–McKendrick SIR model](../../../kermack-mckendrick-sir-model/README.md)

## Expansion

Substituting the ansatz into the PDE and using $\varphi'(A) = -A\varphi(A)$ and $\varphi''(A) = (A^2 - 1)\varphi(A)$, every term becomes $\varphi(A)$ times a polynomial in $A$ with only constant and $A^2$ terms. Setting both coefficients to zero gives the equations for $\lambda$ and $S$; the equation for $I$ follows from $\int\beta(a)\,S(t,a)\,da = S(\beta_0 + \beta_1\lambda^2)$ for the half-normal profile. Differentiating $\bar\beta = \beta_0 + \beta_1\lambda^2$ gives $\dot{\bar\beta} = 2\beta_1\lambda\dot\lambda = -2I\beta_1^2\lambda^4/N - 2\mu_0\beta_1\lambda^2 + 2D\beta_1$.

## Sources

- H. Berestycki, B. Desjardins, J. S. Weitz and J.-M. Oury, "Epidemic modeling with heterogeneity and social diffusion", Journal of Mathematical Biology 86 (2023), article 60, <https://doi.org/10.1007/s00285-022-01861-w> (PMC10039364), sections 2.3 and 4, Equations (11), (26) and (27).
