# Optimality system for chemotherapy control with a tumour-density state constraint

**Setting.** Let $\Omega \subset \mathbb{R}^m$ be a bounded smooth domain (the tumour region) with boundary $\Gamma$, $\mathcal{Q} = (0,T)\times\Omega$, $\Sigma = (0,T)\times\Gamma$. The tumour cell density $u(t,x)$ under a drug concentration $\varphi(t,x)$ solves the reaction–diffusion problem

$$\partial_t u - \operatorname{div}(D(t,x)\nabla u) = K_2u - K_1h_1(u) - \alpha_0\varphi u \ \text{in } \mathcal{Q}, \qquad -D\nabla u\cdot n = K_3h_2(u) \ \text{on } \Sigma, \qquad u(0) = u_0,$$

where $h_i(z) = z^{\rho_i}$ (or $z|z|^{\rho_i-1}$ for non-integer $\rho_i > 1$), $K_1, K_2$ are growth/proliferation coefficients, $K_3$ models invasion through the boundary, and $\alpha_0 > 0$ is the drug kill rate. Admissible controls are $\mathcal{U}_{ad} = \{\varphi \in L^{p_c}(\mathcal{Q}) : a(x) \le \varphi(t,x) \le b(x)\}$ with $0 \le a \le b$, the exponents $\rho_1, \rho_2, p_c$ satisfying explicit compatibility conditions with the integrability of $u_0 \in W^{r,q}(\Omega)$. With $\mathcal{F}(\varphi) = u$ the control-to-state map, the problem is

$$(\mathrm{P}) \qquad \min_{\varphi\in\mathcal{U}_{ad}} J(\varphi) = \frac{1}{2}\int_{\mathcal{Q}}u^2\,dx\,dt + \frac{\lambda}{p_c}\int_{\mathcal{Q}}|\varphi|^{p_c}\,dx\,dt \quad \text{s.t.} \quad \mathcal{G}(\varphi)(t) = \|\mathcal{F}(\varphi)(t)\|_{L^2(\Omega)}^2 - \zeta(t) \le 0 \ \text{for a.e. } t,$$

where $\zeta$ is the maximal tolerated tumour burden.

**Theorem (state equation).** For $u_0 \in W^{r,q}(\Omega)$ ($r \in \{0,1\}$, $q > 1$) and $\varphi \in \mathcal{U}_{ad}$ there is a unique regular local mild solution; if $\rho_1 + 1 > 2\rho_2$ (or equality plus a quantitative condition on $D$, $K_1$, $K_3$), it is a global classical solution on $(0,T)$, depending Lipschitz-continuously (in fractional-power norms) on $(u_0,\varphi)$. If $0 \le u_0 \le c_s$ with $c_s = (\sup K_2/\inf K_1)^{1/(\rho_1-1)}$, then $0 \le u(t,\cdot) \le c_s$ for all $t$ (maximum principle).

**Theorem (existence and optimality).** Problem (P) has at least one optimal control. If $\varphi_*$ is optimal, $u_* = \mathcal{F}(\varphi_*)$, and a Slater-type constraint qualification holds, then there exist an adjoint state $\tilde u_*$ and a non-zero nonnegative measure multiplier $\mu_*$ (a $BV(0,T)$ function with $d\mu_* \ge 0$) such that

$$-\partial_t\tilde u_* - \operatorname{div}(D\nabla\tilde u_*) + \big(K_1h_1'(u_*) - K_2 + \alpha_0\varphi_*\big)\tilde u_* = u_* + 2u_*\,d\mu_*(t), \qquad -D\nabla\tilde u_*\cdot n - K_3h_2'(u_*)\tilde u_* = 0, \qquad \tilde u_*(T) = 0,$$

the complementarity conditions $\mathcal{G}(\varphi_*) \le 0$, $\int_0^T\mathcal{G}(\varphi_*)\,d\mu_* = 0$, $\mu_*(T) = 0$ hold, and for all $\varphi \in \mathcal{U}_{ad}$

$$\int_{\mathcal{Q}}\big(\lambda|\varphi_*|^{p_c-1} - \alpha_0u_*\tilde u_*\big)(\varphi - \varphi_*)\,dx\,dt \ge 0.$$

## Expansion

Well-posedness uses analytic-semigroup theory in Bessel-potential spaces for the linear part and fixed points for the nonlinear reaction and boundary terms; the condition $\rho_1 + 1 \ge 2\rho_2$ lets the interior logistic damping $-K_1u^{\rho_1}$ dominate the boundary flux $K_3u^{\rho_2}$ so that solutions stay bounded. Existence of an optimal control follows from weak compactness of the box-constrained controls in $L^{p_c}$, weak continuity of $\mathcal{F}$, and convexity of the cost. The state constraint is pointwise in time with values in $C([0,T])$, so its multiplier lives in the dual, the space of Radon measures; it acts as a source $2u_*\,d\mu_*$ in the adjoint equation exactly at times when the tumour burden touches $\zeta$. The variational inequality then expresses the optimal dose as a projection of $(\alpha_0u_*\tilde u_*/\lambda)^{1/(p_c-1)}$ onto $[a,b]$.

## Sources

- David Lassounon, Aziz Belmiloudi and Mounir Haddou, "Optimal Control Problem with Mixed Control and State Constraints for Cancer Chemotherapy and Treatment Optimization", arXiv:2606.21765 (2026), Theorems 2.1 and 2.2, Proposition 2.1, Corollary 3.1, Theorems 3.1–3.3, <https://doi.org/10.48550/arXiv.2606.21765>.
