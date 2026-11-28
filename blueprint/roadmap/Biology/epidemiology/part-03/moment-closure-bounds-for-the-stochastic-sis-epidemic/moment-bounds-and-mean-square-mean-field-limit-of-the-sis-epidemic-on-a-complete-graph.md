# Moment bounds and mean-square mean-field limit of the SIS epidemic on a complete graph

**Model.** On the complete graph with $n$ nodes, each infected node infects each susceptible neighbor at rate $\tau/n$ and recovers at rate $\gamma$ (the stochastic SIS, or logistic, epidemic). Let $i_n(t) = I_n(t)/n$ be the infected fraction and let $y$ solve the mean-field (logistic) equation

$$y' = \tau y(1-y) - \gamma y, \qquad y(0) = u.$$

Let $(z_{1,n}, z_{2,n})$ solve the closed system

$$z_{1,n}' = \tau(z_{1,n} - z_{2,n}) - \gamma z_{1,n}, \qquad z_{2,n}' = 2\tau\big(z_{2,n} - z_{2,n}^{3/2}\big) - 2\gamma z_{2,n} + \frac{\tau + \gamma}{n},$$

with $z_{1,n}(0) = u$, $z_{2,n}(0) = u^2$.

**Theorem.** If $i_n(0) = u \in [0,1]$ for all $n$, then for all $t \ge 0$

$$y(t) \ \ge\ \mathbb E[i_n(t)] \ \ge\ z_{1,n}(t), \qquad z_{2,n}(t) \ \ge\ \mathbb E[i_n(t)^2] \ \ge\ z_{1,n}(t)^2,$$

and $z_{1,n} \to y$, $z_{2,n} \to y^2$ uniformly on compact time intervals. Consequently $i_n(t)$ converges to $y(t)$ uniformly in mean square on every finite interval $[0,T]$:

$$\sup_{t \le T}\mathbb E\big[|i_n(t) - y(t)|^2\big] \to 0 \quad (n \to \infty).$$

The upper bound says the deterministic mean-field model always overestimates the expected prevalence of the stochastic SIS epidemic; the lower bound, computable from a two-dimensional ODE, quantifies the error at finite $n$.

## Expansion

Kolmogorov's forward equations give, with $SI = I(n-I)$ the number of susceptible–infected edges, $\mathbb E[i]' = \tau(\mathbb E[i] - \mathbb E[i^2]) - \gamma\mathbb E[i]$ and a similar equation for $\mathbb E[i^2]$ involving $\mathbb E[i^3]$ plus an $O(1/n)$ term. Closing these by Jensen-type inequalities, $\mathbb E[i^2] \ge \mathbb E[i]^2$ and $\mathbb E[i^3] \ge \mathbb E[i^2]^{3/2}$, turns the moment equations into differential inequalities, and a standard ODE comparison lemma gives the upper bound by $y$ and the bounds by $(z_{1,n}, z_{2,n})$. As $n \to \infty$ the $(\tau+\gamma)/n$ forcing vanishes, $z_{2,n} \to z_{1,n}^2$ and both reduce to the logistic equation, so the variance of $i_n(t)$ tends to $0$ uniformly on $[0,T]$. The argument is elementary, avoiding martingale or Kurtz-type limit theorems.

## Sources

- Benjamin Armbruster, Ekkehard Beck, "An elementary proof of convergence to the mean-field equations for an epidemic model", arXiv (2015). Section 2 (Theorem 1), Section 3 (Proposition 2 and proof). <https://doi.org/10.48550/arXiv.1501.03250>. Published version: IMA Journal of Applied Mathematics 82(1) (2017), 152–157, <https://doi.org/10.1093/imamat/hxw010>; locators above refer to the arXiv version.
