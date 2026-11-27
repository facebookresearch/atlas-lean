# HJB feedback harvesting effort under multiplicative environmental noise

**Model.** On a filtered probability space carrying a standard Brownian motion $W$, a renewable resource $X(t) > 0$ is harvested with bounded effort $E(t) \in [0,\bar E]$, $\bar E \in (0,\infty)$ (an adapted control), and evolves as

$$dX(t) = \big[f(X(t))X(t) - qE(t)X(t)\big]\,dt + \sigma X(t)\,dW(t),$$

where $f$ is the per-capita growth rate (locally Lipschitz, with $|f(x)x| \le C_f(1+x)$), $q > 0$ the catchability and $\sigma > 0$ the environmental volatility. The instantaneous profit is

$$\Pi(t) = p\,q\,E(t)X(t) - c_1E(t) - c_2E(t)^2,$$

with price $p > 0$, linear effort cost $c_1 > 0$ and convex effort penalty $c_2 > 0$. The value function on a horizon $[t,T]$ with discount rate $\delta > 0$ is $J^*(t,x) = \sup_E \mathbb{E}\big[\int_t^T e^{-\delta(s-t)}\Pi(s)\,ds \mid X_t = x\big]$, the supremum over adapted controls with values in $[0,\bar E]$, with $J^*(T,x) = 0$.

**HJB equation and feedback law.** With the controlled generator $\mathcal{L}^E\varphi = [f(X)X - qEX]\varphi_X + \tfrac12\sigma^2X^2\varphi_{XX}$, the value function formally solves

$$-\partial_t J^* = \max_{E \in [0,\bar E]}\Big\{pqEX - c_1E - c_2E^2 - \delta J^* + J_X\,[f(X)X - qEX] + \tfrac12\sigma^2X^2J_{XX}\Big\}.$$

The control-dependent Hamiltonian is $H = E\,A(t,X) - c_2E^2$ with $A(t,X) = pqX - c_1 - qXJ_X(t,X)$. Since $\partial_E^2 H = -2c_2 < 0$, the maximizer over $[0,\bar E]$ is unique and is the projection

$$E^*(t,X) = \Pi_{[0,\bar E]}\Big(\frac{A(t,X)}{2c_2}\Big), \qquad \Pi_{[0,\bar E]}(y) = \min\{\bar E, \max\{0, y\}\}:$$

no harvest where $A \le 0$, the interior effort $A/(2c_2)$ where $0 < A < 2c_2\bar E$, and saturation $\bar E$ where $A \ge 2c_2\bar E$. The maximized Hamiltonian is

$$h_{\bar E}(\alpha) = \max_{e \in [0,\bar E]}\{\alpha e - c_2e^2\} = \begin{cases} 0, & \alpha \le 0,\\ \alpha^2/(4c_2), & 0 < \alpha < 2c_2\bar E,\\ \bar E\alpha - c_2\bar E^2, & \alpha \ge 2c_2\bar E,\end{cases}$$

so substituting the projected optimizer gives the constrained reduced HJB equation

$$-\partial_t J^* = f(X)XJ_X + \tfrac12\sigma^2X^2J_{XX} - \delta J^* + h_{\bar E}\big(pqX - c_1 - qXJ_X\big).$$

**Verification (Proposition 3).** Suppose $f$ is locally Lipschitz and, for every admissible control, the state equation has a non-explosive pathwise unique strong solution with the polynomial moment bounds the argument needs. If $V \in C^{1,2}([0,T)\times\mathbb{R}_+) \cap C([0,T]\times\mathbb{R}_+)$ solves the constrained reduced HJB equation with $V(T,\cdot) = 0$ and polynomial growth, and the closed-loop equation driven by the feedback $E_s^* = \Pi_{[0,\bar E]}\big((pqX_s - c_1 - qX_sV_X(s,X_s))/(2c_2)\big)$ has a non-explosive pathwise unique strong solution, then $V = J^*$ and this feedback is optimal among admissible controls.

**Existence and uniqueness (Proposition 4).** Suppose moreover that $J^*$ is a classical solution of the constrained reduced HJB equation with polynomial growth, and that $J^*_X(s,\cdot)$ is Lipschitz and bounded on each $[0,R]$, uniformly in $s \in [0,T)$. Then the closed-loop equation driven by

$$E_s^* = \Pi_{[0,\bar E]}\Big(\frac{pqX_s^* - c_1 - qX_s^*J_X^*(s,X_s^*)}{2c_2}\Big)$$

has a non-explosive pathwise unique strong solution $X^*$, this $E^*$ is admissible and optimal, and every optimal control equals $E^*$ up to a $ds \otimes d\mathbb{P}$-null set.

## Expansion

The marginal value $J_X$ is the shadow price of the standing stock: a larger $J_X$ makes conservation more valuable and lowers optimal effort, and effort is positive only where the current marginal revenue $pqX$ exceeds the linear cost plus the foregone continuation value $qXJ_X$. Verification is the usual argument: apply Itô's formula to $e^{-\delta(s-t)}V(s,X_s)$ along an arbitrary admissible control, use that $eA_V - c_2e^2 \le h_{\bar E}(A_V)$ for every $e \in [0,\bar E]$, with equality only at the projected selector, so that the HJB bracket is non-positive for every admissible effort and zero at $E^*$, then localize and take expectations; the polynomial growth bound and the moment bounds give the uniform integrability that removes the localization. The sign constraint matters: substituting the unconstrained stationary point $A/(2c_2)$ everywhere gives the nonlinearity $A^2/(4c_2)$ of the problem with $E \in \mathbb{R}$, which near $X = 0$ (where $A \to -c_1 < 0$) rewards negative effort and so solves for a strictly larger value than $J^*$. Since the projection is non-expansive, the closed-loop drift inherits the local Lipschitz property of $J^*_X$, which gives the strong solution in Proposition 4; strict concavity of the Hamiltonian in $E$ gives uniqueness of the optimal control. Proposition 2 of the source supplies the dynamic programming principle and finiteness of $J^*$ under Lipschitz and linear-growth coefficients.

## Sources

- Paramahansa Pramanik, Fatamatuj Johora, "Stochastic Optimal Harvesting of Renewable Resources", Journal of Innovation 1 (2026), 4, <https://doi.org/10.3390/joi1010004>. Section 2.3 (Equation (6), Proposition 2) and Section 2.4: HJB equation (7), projected feedback (9), constrained Hamiltonian $h_{\bar E}$ and constrained reduced HJB equation (10), Proposition 3 (p. 16) and Proposition 4 (p. 19). This page follows this version.
- Paramahansa Pramanik and Fatamatuj Johora, *Optimal Harvesting under Stochastic Control: HJB Equation and Feynman–Kac Representation*, arXiv:2606.08428 (2026). <https://doi.org/10.48550/arXiv.2606.08428> Earlier preprint of the article above. Its Section 2.4 states Proposition 3 for the reduced equation with the unconstrained feedback (its Equation (8)), which is not the value of the problem with $E \ge 0$; the page states the constrained form of the published version.
