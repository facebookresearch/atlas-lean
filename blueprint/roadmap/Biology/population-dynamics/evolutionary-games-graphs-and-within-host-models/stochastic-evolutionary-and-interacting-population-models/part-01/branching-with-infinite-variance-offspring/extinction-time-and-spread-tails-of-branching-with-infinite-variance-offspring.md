# Extinction-time and spread tails of branching with infinite-variance offspring

**Setting.** In a continuous-time Bienaymé–Galton–Watson process each particle lives an exponential(1) time and is replaced by $M$ offspring with pgf $f(z) = \mathbb E z^M$ and mean $\mu = f'(1) < \infty$. With $h(z) = f(1-z) - (1-z)$, the survival probability $\bar\phi_t = \mathbb P(\tau_e > t)$ of the extinction time (the height of the tree) solves $\dot{\bar\phi}_t = -h(\bar\phi_t)$, $\bar\phi_0 = 1$. Compare two offspring laws:

- **binary branching**, $f(z) = \pi_0 + \pi_1 z + \pi_2 z^2$, with $h(z) = (1-\mu)z + \pi_2 z^2$;
- **Lamperti's infinite-variance law**, $f(z) = 1 - \mu(1-z) + C(1-z)^{\gamma}$ with $\gamma \in (1,2)$ and $\mu - 1 < C < \mu/\gamma$, with $h(z) = (1-\mu)z + Cz^{\gamma}$ and $\pi_0 = 1-\mu+C$, $\pi_1 = \mu - C\gamma$, $\pi_k = C\gamma(\gamma-1)(2-\gamma)\cdots(k-1-\gamma)/k!$ for $k \ge 2$.

**Theorem (extinction time).** For the Lamperti law,

$$\mathbb P(\tau_e > t) = \left[\frac{e^{-(\gamma-1)(1-\mu)t}}{1 + C\bigl(1 - e^{-(\gamma-1)(1-\mu)t}\bigr)/(1-\mu)}\right]^{1/(\gamma-1)} \qquad (\mu \ne 1),$$

so that:

1. subcritical ($\mu < 1$): $\mathbb P(\tau_e > t) \sim (1 + C/(1-\mu))^{-1/(\gamma-1)}e^{-(1-\mu)t}$, an exponential tail with the same scale $1/(1-\mu)$ as binary branching;
2. critical ($\mu = 1$): $\mathbb P(\tau_e > t) = (1 + C(\gamma-1)t)^{-1/(\gamma-1)}$, a Pareto tail of index $1/(\gamma-1) > 1$, lighter than the Pareto$(1)$ tail $1/(1+\pi_2 t)$ of critical binary branching;
3. supercritical ($\mu > 1$): $\mathbb P(\tau_e > t) \to \bar\rho = ((\mu-1)/C)^{1/(\gamma-1)}$, the explosion probability.

**Theorem (spatial spread in dimension one).** Let particles also perform Brownian motion on $\mathbb R$, and let $p(x)$ be the probability that the process started from one particle at $x > 0$ ever has a descendant at the origin. Then $\tfrac12 p'' = h(p)$ with $p(0) = 1$, $p(\infty) = 0$ (critical and subcritical cases). In the subcritical case $p$ decays exponentially with scale $1/\sqrt{2(1-\mu)}$ for both offspring laws. In the critical case

$$p(x) = (1 + x/x_c)^{-2} \ \text{(binary)}, \qquad p(x) = (1 + x/x_c)^{-2/(\gamma-1)} \ \text{(Lamperti)},$$

for explicit scale factors $x_c$. So infinite offspring variance makes the critical epidemic both shorter-lived and spatially more confined.

## Expansion

With $h(z) = az + Cz^\gamma$ and $a = 1-\mu$, the equation $\dot{\bar\phi} = -a\bar\phi - C\bar\phi^\gamma$ is of Bernoulli type. The substitution $u = \bar\phi^{\,1-\gamma}$ linearizes it to $\dot u = (\gamma-1)(au + C)$, $u(0) = 1$, which integrates to the displayed formula. Letting $a \to 0$ gives $u = 1 + (\gamma-1)Ct$. For the spatial problem, $1 - p(x)$ is the probability that no particle ever reaches $0$. A first-branching decomposition gives the stationary Kolmogorov–Petrovskii–Piskunov-type ODE $\tfrac12 p'' = h(p)$. In the critical case $h(p) = Cp^\gamma$, and the power ansatz $p = (1+x/x_c)^{-\alpha}$ balances exactly when $\alpha(\gamma-1) = 2$.

## Sources

- Jean Avan, Nicolas Grosjean, Thierry Huillet, "On the spread of a branching Brownian motion whose offspring number has infinite variance", arXiv (2014). Section 2 (Models 1 and 2, Propositions 1–2), Section 3 (Propositions 7–8). <https://doi.org/10.48550/arXiv.1402.5389>. Published version: Jean Avan, Nicolas Grosjean, Thierry Huillet, "On extreme events for non-spatial and spatial branching Brownian motions", Physica D: Nonlinear Phenomena 298–299 (2015), 13–20, <https://doi.org/10.1016/j.physd.2015.01.008>; locators above refer to the arXiv version.
