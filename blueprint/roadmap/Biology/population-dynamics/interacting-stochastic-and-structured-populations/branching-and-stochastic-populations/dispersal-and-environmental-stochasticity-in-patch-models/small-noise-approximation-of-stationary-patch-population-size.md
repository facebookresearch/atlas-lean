# Small-noise approximation of stationary patch population size

**Setting.** Write the stochastic [patch model](lyapunov-exponent-classification-of-stochastic-patch-models.md) as $\mathbf N(t+1) = F(\mathbf N(t), e(t))$ with environmental parameters $e(t) = \bar e + \rho\,\xi(t)$, where $(e(t))$ is i.i.d. with values in a compact convex set and $0 \le \rho \ll 1$ measures the noise. Suppose the deterministic system $\bar{\mathbf N}(t+1) = F(\bar{\mathbf N}(t), \bar e)$ satisfies the hypotheses of the deterministic classification with $\lambda(D(\bar e)\Lambda(0,\bar e)) > 1$, so it has a unique globally attracting equilibrium $\bar{\mathbf N}_0$, assumed hyperbolic.

**Theorem 4.1 and Theorem A.2.** Under these assumptions the stochastic system has an invariant probability measure $\mu$ with $\bar{\mathbf N}_0 \in \mathrm{supp}\,\mu$, supported in a small ball around $\bar{\mathbf N}_0$ for small $\rho$, and the population converges to it in distribution from initial states near $\bar{\mathbf N}_0$. Let $D_N F$ and $D_\xi F$ be the Jacobians of $F$ in the populations and the noise at $(\bar{\mathbf N}_0, \bar e)$, and $B = (I - D_N F)^{-1}$. If $\mathbf N \sim \mu$, then

$$\mathbb E\mathbf N = \bar{\mathbf N}_0 + \rho\, B D_\xi F\, \mathbb E\xi + \frac12 B\sum_{i,j}\frac{\partial^2 F}{\partial N_i\partial N_j}[\mathrm{Cov}\,\mathbf N]_{ij} + \frac{\rho^2}{2} B\sum_{i,j}\frac{\partial^2 F}{\partial\xi_i\partial\xi_j}\big([\mathrm{Cov}\,\xi]_{ij} + \mathbb E\xi_i\,\mathbb E\xi_j\big) + R_2 + O(\rho^3),$$

where, with $m = B D_\xi F\,\mathbb E\xi$ and all derivatives at $(\bar{\mathbf N}_0, \bar e)$,

$$R_2 = \frac{\rho^2}{2} B\sum_{i,j}\frac{\partial^2 F}{\partial N_i\partial N_j}\,m_i m_j + \rho^2 B\sum_{i,j}\frac{\partial^2 F}{\partial N_i\partial\xi_j}\,(\mathbb E\xi)_j\, m_i ,$$

and, to leading order, the stationary covariance solves the discrete Lyapunov equation

$$\mathrm{vec}(\mathrm{Cov}\,\mathbf N) = \rho^2\,(I - D_N F \otimes D_N F)^{-1}(D_\xi F \otimes D_\xi F)\,\mathrm{vec}(\mathrm{Cov}\,\xi).$$

The source prints the covariance equation without the factor $\rho^2$; it is needed, since $e = \bar e + \rho\xi$ enters only through $\rho\xi$. In one dimension, $F(N,e) = aN + e$ with $|a| < 1$ and $\mathrm{Var}\,\xi = \sigma^2$ has $\mathrm{Var}\,N = \rho^2\sigma^2/(1-a^2)$. So $\mathrm{Cov}\,\mathbf N = O(\rho^2)$, and the second term of $\mathbb E\mathbf N$ is of order $\rho^2$.

For centered noise ($\mathbb E\xi = 0$) the first-order term vanishes and the noise-induced change $\mathbb E\mathbf N - \bar{\mathbf N}_0$ is of order $\rho^2$, with a sign set by the curvature of $F$ and by the covariances among growth rates, carrying capacities and dispersal rates.

**Single-patch benchmark (Remark 2.7).** For the Beverton-Holt map $N_{t+1} = mK_t N_t/(K_t + (m-1)N_t)$ with $m > 1$ and only the carrying capacity $K_t$ random, the stationary mean satisfies $\mathbb E N(\infty) < \mathbb E K_1$ (the Cushing-Henson conjecture), so in the small-dispersal limit fluctuating carrying capacities always lower the total expected population size. In the Hassell model with a random inverse carrying capacity, fluctuations instead raise it.

## Expansion

The expansion is a stochastic analogue of the delta method: write $\mathbf N = \bar{\mathbf N}_0 + \rho\mathbf X$, Taylor-expand $F$ to second order around $(\bar{\mathbf N}_0, \bar e)$, take expectations under the stationary law, and solve the resulting linear equations, which involve $(I - D_N F)^{-1}$ because $\bar{\mathbf N}_0$ is a stable fixed point (all eigenvalues of $D_N F$ inside the unit disc). The covariance equation is $\rho^2$ times the stationary covariance of the linearized recursion $\mathbf X(t+1) = D_N F\,\mathbf X(t) + D_\xi F\,\xi(t)$, as $\mathrm{Cov}\,\mathbf N = \rho^2\,\mathrm{Cov}\,\mathbf X$. Small noise cannot produce a negative metapopulation growth rate: convergence to a measure near $\bar{\mathbf N}_0$ is incompatible with extinction, so $M > 0$ (Remark A.1). The two-patch formulas show that the covariance between, for example, growth rate and dispersal decides whether noise increases or decreases the total population.

## Depends on

- [Lyapunov exponent classification of stochastic patch models](lyapunov-exponent-classification-of-stochastic-patch-models.md)

## Sources

- A. Hening, S. Sabharwal, "Population size in stochastic multi-patch ecological models", *Journal of Mathematical Biology* 92(3) (2026), 43, Remark 2.7, Section 4 (Theorem 4.1, Eq. (26)), Appendix A (Assumption A.1, Theorems A.1 and A.2, Remark A.1), <https://doi.org/10.1007/s00285-026-02365-7> (preprint arXiv:2511.19743).
