# HJB feedback harvesting effort under multiplicative environmental noise

**Model.** On a filtered probability space carrying a standard Brownian motion $W$, a renewable resource $X(t) > 0$ is harvested with effort $E(t) \ge 0$ (an adapted control) and evolves as

$$dX(t) = \big[f(X(t))X(t) - qE(t)X(t)\big]\,dt + \sigma X(t)\,dW(t),$$

where $f$ is the per-capita growth rate (locally Lipschitz, linear growth), $q > 0$ the catchability and $\sigma > 0$ the environmental volatility. The instantaneous profit is

$$\Pi(t) = p\,q\,E(t)X(t) - c_1E(t) - c_2E(t)^2,$$

with price $p > 0$, linear effort cost $c_1 > 0$ and convex effort penalty $c_2 > 0$. The value function on a horizon $[t,T]$ with discount rate $\delta > 0$ is $J^*(t,x) = \sup_E \mathbb{E}\big[\int_t^T e^{-\delta(s-t)}\Pi(s)\,ds \mid X_t = x\big]$, with $J^*(T,x) = 0$.

**HJB equation and feedback law.** With the controlled generator $\mathcal{L}^E\varphi = [f(X)X - qEX]\varphi_X + \tfrac12\sigma^2X^2\varphi_{XX}$, the value function formally solves

$$-\partial_t J^* = \max_{E \ge 0}\Big\{pqEX - c_1E - c_2E^2 - \delta J^* + J_X\,[f(X)X - qEX] + \tfrac12\sigma^2X^2J_{XX}\Big\}.$$

The control-dependent Hamiltonian $H = E\,(pqX - c_1 - qXJ_X) - c_2E^2$ has $\partial_E^2 H = -2c_2 < 0$, so the maximizer is unique and given by

$$E^*(t,X) = \max\Big\{0,\ \frac{pqX - c_1 - qXJ_X(t,X)}{2c_2}\Big\}.$$

Substituting the interior optimizer gives the reduced nonlinear HJB equation

$$-\partial_t J^* = f(X)XJ_X + \tfrac12\sigma^2X^2J_{XX} - \delta J^* + \frac{(pqX - c_1 - qXJ_X)^2}{4c_2}.$$

**Verification (Proposition 3).** If $f$ is locally Lipschitz with linear growth and $V \in C^{1,2}([0,T)\times\mathbb{R}_+) \cap C([0,T]\times\mathbb{R}_+)$ solves the reduced HJB equation with $V(T,\cdot) = 0$ and polynomial growth, then $V = J^*$ and the feedback law above is optimal.

**Existence and uniqueness (Proposition 4).** If effort is restricted to $E_s \in [0,\bar E]$ with $\bar E < \infty$ and $J^*$ is a classical solution of the HJB equation with polynomial growth, the optimal control is unique up to $ds \otimes d\mathbb{P}$-null sets and is the projection

$$E_s^* = \min\Big\{\bar E,\ \max\Big\{0,\ \frac{pqX_s^* - c_1 - qX_s^*J_X^*(s,X_s^*)}{2c_2}\Big\}\Big\},$$

where $X^*$ is the strong solution of the state equation driven by $E^*$.

## Expansion

The marginal value $J_X$ is the shadow price of the standing stock: a larger $J_X$ makes conservation more valuable and lowers optimal effort, and effort is positive only where the current marginal revenue $pqX$ exceeds the linear cost plus the foregone continuation value $qXJ_X$. Verification is the usual argument: apply Itô's formula to $e^{-\delta(s-t)}V(s,X_s)$ along an arbitrary admissible control, use that the HJB bracket is non-positive for every effort and zero at $E^*$, and take expectations; the polynomial growth bound kills the local-martingale term. Strict concavity of the Hamiltonian in $E$ gives uniqueness of the pointwise maximizer and hence of the optimal control. Proposition 2 of the source supplies the dynamic programming principle and finiteness of $J^*$ under Lipschitz and linear-growth coefficients.

## Sources

- Paramahansa Pramanik, Fatamatuj Johora, "Stochastic Optimal Harvesting of Renewable Resources", Journal of Innovation 1 (2026), 4, <https://doi.org/10.3390/joi1010004>. Published version of arXiv:2606.08428, cited next; locators there refer to the arXiv version.
- Paramahansa Pramanik and Fatamatuj Johora, *Optimal Harvesting under Stochastic Control: HJB Equation and Feynman–Kac Representation*, arXiv:2606.08428 (2026). <https://doi.org/10.48550/arXiv.2606.08428> Section 2.3 (profit and value function, Proposition 2), Section 2.4 (HJB equation, feedback law, reduced HJB, Propositions 3 and 4).
