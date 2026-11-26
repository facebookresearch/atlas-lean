# Rank-one adjoint and bang-bang size-selective harvesting

**Setting.** For the size-structured model with environmental output $E = \int_\Omega \chi x$, fixed recruitment flux and stationary harvest $u(l) \in [0, u_{\max}]$, let $(x^*, E^*)$ be a stationary state solving the closure equation $E^* = \Phi_u(E^*)$, as in [the environmental closure map](environmental-closure-map-and-fold-resonance-for-size-structured-harvesting.md), and consider maximizing the yield $\mathcal Y(u) = \int_\Omega \pi u x^*_u\,dl$. Put $g^* = g(E^*,\cdot)$, $\mu^* = \mu(E^*,\cdot)$, $a = \partial_E g(E^*,\cdot)\, x^*$, $m = \partial_E \mu(E^*,\cdot)\, x^*$, the adjoint operator $\mathcal L_0^* \lambda = -g^* \lambda' + (\mu^* + u)\lambda$ with $\lambda(l_m) = 0$, its inverse $R_0$, and the co-load functional
$$\langle \sigma, \lambda \rangle = \int_\Omega \bigl(a \lambda' - m\lambda\bigr)\,dl.$$
Let $\psi_0 = R_0 \chi$, $\lambda_{\mathrm{red}} = R_0(\pi u)$, $A_0 = \langle\sigma, \lambda_{\mathrm{red}}\rangle$, $B_0 = \langle\sigma, \psi_0\rangle$.

**Theorem 3.9 (Lagrangian adjoint).** At a local maximizer $u^*$ with $1 - \Phi_u'(E^*) \ne 0$, inactive total-variation constraint and a surjectivity constraint qualification, there is a multiplier $\lambda$ with $\lambda(l_m) = 0$ solving the rank-one perturbed adjoint equation
$$\bigl(\mathcal L_0^* - \chi \langle\sigma, \cdot\rangle\bigr)\lambda = \pi u^*,$$
together with the variational inequality $\int_\Omega x^*(\pi - \lambda)(v - u^*)\,dl \le 0$ for all $0 \le v \le u_{\max}$.

**Theorem 3.10 (Sherman-Morrison reduction).** If $1 - B_0 \ne 0$, the adjoint equation has the unique solution
$$\lambda = \lambda_{\mathrm{red}} + \frac{A_0}{1 - B_0}\,\psi_0.$$
If $1 - B_0 = 0$ (and $\psi_0 \not\equiv 0$), then $\psi_0$ spans a kernel direction and the equation is solvable iff $A_0 = 0$.

**Theorem 3.11 (forward-adjoint identity).** $B_0 = \langle\sigma, \psi_0\rangle = \Phi_u'(E^*)$. Hence the adjoint becomes singular exactly at a fold (resonance) of the closure equation.

**Theorem 3.13 (bang-bang law).** With the switching function $S = \pi - \lambda = S_{\mathrm{red}} - \Gamma_0 \psi_0$, where $S_{\mathrm{red}} = \pi - \lambda_{\mathrm{red}}$ and $\Gamma_0 = A_0/(1 - B_0)$, a regular local maximizer satisfies, almost everywhere,
$$u^*(l) = u_{\max} \ \text{if } S(l) > 0, \qquad u^*(l) = 0 \ \text{if } S(l) < 0.$$

**Theorem 3.14 (single-threshold preservation).** If $S_{\mathrm{red}}$ has a unique simple zero $l_{\mathrm{red}}$ and the feedback correction is small, namely $|\Gamma_0|\,\|\psi_0\|_\infty < \inf_{\Omega \setminus N_\delta}|S_{\mathrm{red}}|$ and $|\Gamma_0|\,\|\psi_0'\|_{L^\infty(N_\delta)} < \inf_{N_\delta}|S_{\mathrm{red}}'|$ on a neighbourhood $N_\delta$ of $l_{\mathrm{red}}$, then $S$ has exactly one zero $l_*$, and
$$l_* - l_{\mathrm{red}} = \frac{\Gamma_0\, \psi_0(l_{\mathrm{red}})}{S_{\mathrm{red}}'(l_{\mathrm{red}})} + o(|\Gamma_0|).$$
Larger corrections can create new harvest windows through a tangency (fold) of $S$ (Theorem 3.15).

## Expansion

Because the coefficients depend on the state only through the scalar $E$, linearizing the closure adds to the ordinary adjoint operator a rank-one term $\chi\langle\sigma,\cdot\rangle$: the environmental weight times the sensitivity of growth and mortality to $E$. The Sherman-Morrison formula inverts a rank-one perturbation of an invertible operator, giving the reduced adjoint $\lambda_{\mathrm{red}}$ (the adjoint with the environment frozen) plus a feedback correction along $\psi_0$. Testing the forward sensitivity equation for $y = \partial_E x_E$ against $\psi_0$ and integrating by parts, the fixed-flux boundary condition makes the boundary term $(g^* y + a)(l_0)$ vanish, which yields $B_0 = \int_\Omega \chi y = \Phi_u'(E^*)$. The control enters the Hamiltonian linearly as $u\,x^*(\pi - \lambda)$ with $x^* > 0$, so the pointwise maximum condition is bang-bang in the sign of $S$, and a perturbation estimate on a transversal zero gives the threshold shift.

## Depends on

- [Environmental closure map and fold resonance for size-structured harvesting](environmental-closure-map-and-fold-resonance-for-size-structured-harvesting.md)

## Sources

- L. S. Wang, J. Yu, "Optimal harvesting of size-structured populations with environmental feedback and fixed recruitment flux" (2026), Section 3 (Theorems 3.9, 3.10, 3.11, 3.13, 3.14 and 3.15, Corollary 3.12), <https://doi.org/10.48550/arXiv.2607.03790>.
