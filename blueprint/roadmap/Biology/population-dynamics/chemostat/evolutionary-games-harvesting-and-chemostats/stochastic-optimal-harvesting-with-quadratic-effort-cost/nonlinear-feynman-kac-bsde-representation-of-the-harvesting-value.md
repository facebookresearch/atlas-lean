# Nonlinear Feynman–Kac (BSDE) representation of the harvesting value

Consider the stochastic harvesting problem with state $dX = [f(X)X - qEX]\,dt + \sigma X\,dW$, bounded effort $E \in [0,\bar E]$, profit $pqEX - c_1E - c_2E^2$ ($c_2 > 0$, $\sigma > 0$), discount rate $\delta > 0$ and terminal condition $J^*(T,\cdot) = 0$, whose value function $J^*$ solves the constrained reduced HJB equation

$$\partial_t J^* + f(X)XJ^*_X + \tfrac12\sigma^2X^2J^*_{XX} - \delta J^* + h_{\bar E}\big(pqX - c_1 - qXJ^*_X\big) = 0,$$

with the constrained Hamiltonian $h_{\bar E}(\alpha) = \max_{e \in [0,\bar E]}\{\alpha e - c_2e^2\}$. Let $X$ be the reference (unharvested) diffusion $dX_s = f(X_s)X_s\,ds + \sigma X_s\,dW_s$, $X_t = x$, and set

$$Y_s = J^*(s,X_s), \qquad Z_s = \sigma X_s\,J^*_X(s,X_s).$$

Since $J_X^* = Z/(\sigma X)$ when $X > 0$, the Hamiltonian term can be written in $(Y,Z)$ and the driver is

$$F(x,y,z) = -\delta y + h_{\bar E}\Big(pqx - c_1 - \frac{qz}{\sigma}\Big).$$

**Proposition 5 (Feynman–Kac representation).** Suppose $J^* \in C^{1,2}([0,T)\times\mathbb{R}_+) \cap C([0,T]\times\mathbb{R}_+)$ is a classical solution of the constrained reduced HJB equation with $J^*(T,\cdot) = 0$, and $J^*$ and $J^*_X$ satisfy polynomial growth bounds ensuring $Y \in \mathcal{S}^2$ and $Z \in \mathcal{H}^2$. Then $(Y,Z)$ solves the backward SDE

$$dY_s = -F(X_s,Y_s,Z_s)\,ds + Z_s\,dW_s, \qquad Y_T = 0,$$

and it is the unique solution in $\mathcal{S}^2 \times \mathcal{H}^2$. Conversely, if $(Y,Z) \in \mathcal{S}^2 \times \mathcal{H}^2$ solves this BSDE and $Y_s = u(s,X_s)$ with $u \in C^{1,2}([0,T)\times\mathbb{R}_+) \cap C([0,T]\times\mathbb{R}_+)$, then $Z_s = \sigma X_s u_x(s,X_s)$, $u$ solves the constrained reduced HJB equation with $u(T,\cdot) = 0$, and, under uniqueness in the prescribed growth class, $u = J^*$ and $Y_t = J^*(t,x)$.

**Proposition 6 (equivalence of the two characterizations).** Under the hypotheses of Proposition 5 and of the existence and uniqueness result for the constrained optimal control, put $\Lambda_s = pqX_s - c_1 - qZ_s/\sigma$. The HJB equation and the BSDE determine the same value function, $Y_t = J^*(t,x)$, the same maximized Hamiltonian, $h_{\bar E}(\Lambda_t) = h_{\bar E}(pqX_t - c_1 - qX_tJ^*_X(t,X_t))$, and the same optimal effort:

$$E^*_{\mathrm{FK}} = \Pi_{[0,\bar E]}\Big(\frac{\Lambda_t}{2c_2}\Big) = \Pi_{[0,\bar E]}\Big(\frac{pqX_t - c_1 - qX_tJ^*_X(t,X_t)}{2c_2}\Big) = E^*_{\mathrm{HJB}}(t,X_t),$$

where $\Pi_{[0,\bar E]}(y) = \min\{\bar E, \max\{0, y\}\}$.

## Depends on

- [HJB feedback harvesting effort under multiplicative environmental noise](hjb-feedback-harvesting-effort-under-multiplicative-noise.md)

## Expansion

The classical (linear) Feynman–Kac formula does not apply because the reduced HJB equation depends nonlinearly on the gradient through $h_{\bar E}$. Applying Itô's formula to $J^*(s,X_s)$ along the reference diffusion, whose generator has no harvesting term, and using the PDE to cancel the generator terms leaves exactly $-F\,ds + \sigma X J^*_X\,dW$, which identifies the BSDE and its martingale integrand $Z$. Because effort is bounded, $h_{\bar E}$ is differentiable with $h_{\bar E}'(\alpha) = \Pi_{[0,\bar E]}(\alpha/(2c_2)) \in [0,\bar E]$, so the driver is globally Lipschitz in $z$ (constant $q\bar E/\sigma$) and in $y$, and uniqueness follows from standard Lipschitz-BSDE theory rather than quadratic-growth results. The equivalence is algebraic: $Z$ is the diffusion-weighted gradient of the value function, so the argument $\Lambda$ of the BSDE Hamiltonian equals the argument $A$ of the HJB Hamiltonian along the state, and the two projected selectors coincide pathwise, with the same no-harvest, interior and saturation regimes. In this representation $Z_s$ reads as the sensitivity of the harvesting value to environmental shocks.

## Sources

- Paramahansa Pramanik, Fatamatuj Johora, "Stochastic Optimal Harvesting of Renewable Resources", Journal of Innovation 1 (2026), 4, <https://doi.org/10.3390/joi1010004>. Section 2.5 (driver (11), BSDE (12), Proposition 5, p. 24) and Section 2.6 (Proposition 6, p. 27). This page follows this version.
- Paramahansa Pramanik and Fatamatuj Johora, *Optimal Harvesting under Stochastic Control: HJB Equation and Feynman–Kac Representation*, arXiv:2606.08428 (2026). <https://doi.org/10.48550/arXiv.2606.08428> Earlier preprint of the article above. Its Sections 2.5–2.6 use the unconstrained quadratic driver and feedback; the page states the constrained form of the published version.
