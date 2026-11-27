# Nonlinear Feynman–Kac (BSDE) representation of the harvesting value

Consider the stochastic harvesting problem with state $dX = [f(X)X - qEX]\,dt + \sigma X\,dW$, profit $pqEX - c_1E - c_2E^2$ ($c_2 > 0$, $\sigma > 0$), discount rate $\delta > 0$ and terminal condition $J^*(T,\cdot) = 0$, whose value function $J^*$ solves the reduced HJB equation with a quadratic gradient term. Along the optimally controlled state, set

$$Y_s = J^*(s,X_s), \qquad Z_s = \sigma X_s\,J^*_X(s,X_s).$$

Since $J_X^* = Z/(\sigma X)$ when $X > 0$, the quadratic gradient term can be written in $(Y,Z)$ and the driver is

$$F(x,y,z) = -\delta y + \frac{\big(pqx - c_1 - qz/\sigma\big)^2}{4c_2}.$$

**Proposition 5 (Feynman–Kac representation).** Suppose the state equation has a unique strong solution, $J^*$ is a classical solution of the reduced HJB equation with polynomial growth, and $F$ satisfies the standard quadratic-growth conditions of BSDE theory. Then $(Y,Z)$ is the unique adapted solution in $\mathcal{S}^2 \times \mathcal{H}^2$ of the backward SDE

$$dY_s = -F(X_s,Y_s,Z_s)\,ds + Z_s\,dW_s, \qquad Y_T = 0.$$

Conversely, if $(Y,Z) \in \mathcal{S}^2 \times \mathcal{H}^2$ solves this BSDE and $Y_s = u(s,X_s)$ for a sufficiently smooth $u$, then $u$ solves the reduced HJB equation and $u(t,x) = J^*(t,x) = Y_t$.

**Proposition 6 (equivalence of the two characterizations).** Under the same hypotheses, the HJB equation and the BSDE determine the same value function, $J^*_{\mathrm{HJB}}(t,x) = J^*_{\mathrm{FK}}(t,x) = Y_t$, and the same optimal effort, since

$$E^*_{\mathrm{HJB}} = \frac{pqX - c_1 - qXJ_X}{2c_2} = \frac{pqX - c_1 - qZ/\sigma}{2c_2} = E^*_{\mathrm{FK}}.$$

## Depends on

- [HJB feedback harvesting effort under multiplicative environmental noise](hjb-feedback-harvesting-effort-under-multiplicative-noise.md)

## Expansion

The classical (linear) Feynman–Kac formula does not apply because the reduced HJB equation contains the squared gradient $(qXJ_X)^2/(4c_2)$. Applying Itô's formula to $J^*(s,X_s)$ and using the PDE to cancel the generator terms leaves exactly $-F\,ds + \sigma X J_X\,dW$, which identifies the BSDE and its martingale integrand $Z$. Uniqueness comes from quadratic-BSDE theory (Kobylanski-type results) under the stated growth conditions. The equivalence is algebraic: $Z$ is the diffusion-weighted gradient of the value function, so the HJB feedback written through $J_X$ and the probabilistic feedback written through $Z$ coincide pathwise. In this representation $Z_s$ reads as the sensitivity of the harvesting value to environmental shocks.

## Sources

- Paramahansa Pramanik, Fatamatuj Johora, "Stochastic Optimal Harvesting of Renewable Resources", Journal of Innovation 1 (2026), 4, <https://doi.org/10.3390/joi1010004>. Published version of arXiv:2606.08428, cited next; locators there refer to the arXiv version.
- Paramahansa Pramanik and Fatamatuj Johora, *Optimal Harvesting under Stochastic Control: HJB Equation and Feynman–Kac Representation*, arXiv:2606.08428 (2026). <https://doi.org/10.48550/arXiv.2606.08428> Section 2.5 (driver, BSDE and Proposition 5) and Section 2.6 (Proposition 6).
