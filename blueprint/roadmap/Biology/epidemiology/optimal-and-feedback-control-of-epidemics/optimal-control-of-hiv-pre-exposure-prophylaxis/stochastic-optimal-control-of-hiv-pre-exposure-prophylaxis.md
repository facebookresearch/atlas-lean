# Stochastic optimal control of HIV pre-exposure prophylaxis

**Setting.** On a filtered probability space carrying a Brownian motion $B$, susceptibles $S$, HIV-infected individuals without AIDS symptoms $I$, individuals in the chronic stage $C$, individuals with AIDS clinical symptoms $A$ and PrEP users $E$ evolve by

$$dS = \big[\Lambda - \beta\,\Phi\,S - (\mu + \psi + u)\,S + \theta E\big]dt - \sigma\,\Phi\,S\,dB, \qquad dI = \big[\beta\,\Phi\,S - \xi_3 I + \alpha A + \omega C\big]dt + \sigma\,\Phi\,S\,dB,$$

$$dC = [\phi I - \xi_2 C]\,dt, \qquad dA = [\rho I - \xi_1 A]\,dt, \qquad dE = [\psi S + u S - \xi_4 E]\,dt,$$

with force of infection $\Phi = I + \eta_C C + \eta_A A$, $\xi_1 = \alpha + \mu + d$, $\xi_2 = \omega + \mu$, $\xi_3 = \rho + \phi + \mu$, $\xi_4 = \mu + \theta$, and an adapted control $u(t) \in [0,1]$, the additional fraction of susceptibles put on PrEP. The cost is

$$J(u) = \mathbb{E}\Big[\int_0^T \big(w_1 I(t) + w_2\,u(t)^2\big)\,dt\Big], \qquad w_1, w_2 > 0.$$

**Theorem.**
1. (Well-posedness.) For every positive initial state the controlled system has a unique global solution that stays in $\mathbb{R}^5_{+}$ almost surely, and the total population satisfies $N(t) \to \Lambda/\mu$.
2. (Optimal PrEP rate.) The optimal control is

$$\hat u(t) = \min\Big\{\max\Big\{0,\ \frac{S(t)\,\big(p_1(t) - p_5(t)\big)}{2 w_2}\Big\},\ 1\Big\},$$

where $(p,q)$ is the unique solution of the linear adjoint backward SDE system of the stochastic maximum principle and $p_1, p_5$ are the adjoints of $S$ and $E$.
3. (Budget constraints by Lagrange multipliers.) For a constraint $\mathbb{E}\big[\int_0^T M(t,X,u)\,dt\big] = 0$ (Type I) or $\int_0^T M(t,X,u)\,dt = 0$ almost surely (Type II), suppose the penalised unconstrained problem with multiplier $\lambda \in \mathbb{R}$ (Type I) or random multiplier $\mu$ (Type II) is solvable by $u^\ast_\lambda$. If some $\lambda_0$ makes $u^\ast_{\lambda_0}$ satisfy the constraint, then $u^\ast_{\lambda_0}$ solves the constrained problem; for inequality constraints the same holds with $\lambda_0 \ge 0$ (respectively $\mu_0 \ge 0$ almost surely).

## Expansion

Positivity and global existence follow from a Lyapunov argument on $\sum \log$ of the components, as for the uncontrolled stochastic HIV/PrEP model, because $u \in [0,1]$ enters only as a bounded extra removal rate from $S$ to $E$. The Hamiltonian is $H = w_1 I + w_2 u^2 + p \cdot b(X,u) + q \cdot \sigma(X)$, whose $u$-dependent part is $w_2 u^2 - u\,S\,(p_1 - p_5)$, a convex parabola; minimising it over $[0,1]$ gives the clipped formula, which reads as "put more people on PrEP when the shadow value of a susceptible exceeds that of a PrEP user, scaled by the number of susceptibles". The Lagrange theorems are the stochastic analogue of weak duality: if the penalised optimum happens to be feasible, no feasible control can beat it, since it beats every control on the penalised objective and the penalty vanishes on the feasible set. A budget such as $S(t)u(t) \le \mathcal{V}$ is handled this way after relaxing it to an expected or pathwise integral constraint.

## Sources

- Jasmina Ɖorđević, Kristina Rognlien Dahl, "Stochastic optimal control of pre-exposure prophylaxis for HIV infection for a jump model", Journal of Mathematical Biology 89 (2024), 55, <https://doi.org/10.1007/s00285-024-02151-3>. Published version of arXiv:2009.03594, cited next; locators there refer to the arXiv version.
- Kristina Rognlien Dahl, Jasmina Djordjević, "Stochastic optimal control of pre-exposure prophylaxis for HIV infection", arXiv:2009.03594 (2020), Section 2 (SDE system, Theorem 2.1), Section 3 (cost functional), Theorem 4.2 with the adjoint BSDE system, and Theorems 5.2, 5.4, 5.5 and 5.6, <https://doi.org/10.48550/arXiv.2009.03594>.
