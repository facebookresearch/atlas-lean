# Density threshold for SIS epidemics among customers migrating between $\cdot/M/\infty$ stations

**Model.** A closed network has $N$ stations and $K_N$ customers with $K_N/N \to \eta > 0$ (customer density). Each station is a $\cdot/M/\infty$ queue: every customer leaves its station at rate $\mu$ and moves to a uniformly random other station. Each customer is susceptible ($S$) or infected ($I$), and states change only inside stations: a susceptible customer in a station holding $Y$ infected customers becomes infected at rate $\alpha Y$, and an infected customer recovers at rate $\beta$. The *thermodynamic limit* is $N \to \infty$; under a propagation-of-chaos ansatz a single station becomes an open queue fed by a Poisson stream of arrivals at rate $\lambda = \eta\mu$, each arrival infected with the stationary infected fraction $p$, and $p$ must solve a fixed-point equation $p = g(p)$ with $g(0) = 0$. *Survival* means a stationary regime with $p \in (0,1)$; *strong extinction* means convergence to an infection-free regime from every initial condition.

**Theorem (phase transition in the density).** Assume the propagation-of-chaos ansatz.
1. There is $\eta_c = \eta_c(\alpha, \beta, \mu) \in [0, \infty]$ such that: $\partial_p g(0,\eta) \le 1$ iff $p = 0$ is the only fixed point iff $\eta \le \eta_c$; and $\partial_p g(0,\eta) > 1$ iff there are exactly two fixed points $0$ and $p^* > 0$ iff $\eta > \eta_c$.
2. The threshold is finite and positive:

$$\frac{\beta}{2\mu + 5\beta} \;\le\; \eta_c \;\le\; \frac{1}{\kappa}\,\frac{\beta}{\mu + \beta}, \qquad \kappa = \frac{2\alpha\mu}{2(\mu+\beta)(\alpha + 2\mu + \beta) - \alpha\beta}.$$

3. The epidemic survives if $\eta > \eta_c$ and goes strongly extinct if $\eta \le \eta_c$. Likewise, for fixed other parameters there are thresholds $\alpha_c$ and $\beta_c$ with survival iff $\alpha > \alpha_c$ (respectively $\beta < \beta_c$).

**Averaged-infection-rate variant (AIR).** If each susceptible in a station is infected at a constant rate (the network averaged infection pressure) instead of $\alpha Y$, the station is a product-form Jackson network. Under the corresponding ansatz there is again a threshold $\eta_c^{(a)}$ with weak extinction for $\eta \le \eta_c^{(a)}$ and survival above it, and in the surviving stationary regime the numbers $\widetilde X$ of susceptible and $\widetilde Y$ of infected customers in a station are independent Poisson variables with

$$\mathbb{E}\widetilde X = \frac{\beta}{\alpha}, \qquad \mathbb{E}\widetilde Y = \eta - \frac{\beta}{\alpha},$$

so the susceptible fraction is $\beta/(\eta\alpha)$ and the departure rate per station is $\eta\mu$.

## Expansion

Conditioned on the stationary input stream, one station is a two-type $M/M/\infty$ system whose generating function solves a wave-type PDE; $g(p)$ is the infected fraction of departures when arrivals are infected with probability $p$. Monotonicity and convexity of $g$ in $p$ and monotonicity in $\eta$ (more customers per station make infection more likely before departure) give the dichotomy at $g'(0) = 1$. The bounds follow by comparing with explicit sub- and super-solutions: crude estimates of the probability that a newly arrived susceptible is infected before leaving, given one infected companion. In the AIR model the infection rate does not depend on the local infected count, so stations decouple into independent infinite-server queues and the stationary law is product-form Poisson.

## Sources

- F. Baccelli, S. Foss and V. Shneer, "Migration-Contagion Processes", *Advances in Applied Probability* 56(1) (2023), 71–105, Corollaries 13, 15, 17, Theorems 19, 20, 22 and 23, <https://doi.org/10.1017/apr.2023.17> (preprint arXiv:2208.03512).
