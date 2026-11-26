# Optimal controls under vanishing hyperbolic relaxation in a phase-field tumor model

**Model.** Let $\Omega \subset \mathbb{R}^3$ be a bounded smooth domain, $T > 0$, $Q = \Omega \times (0,T)$. For a relaxation parameter $\alpha \ge 0$ the state $(\mu, \varphi, \sigma)$ (chemical potential, tumor phase field, nutrient concentration) solves

$$\alpha\,\partial_{tt}\mu + \partial_t\varphi - \Delta\mu = P(\varphi)\big(\sigma + \chi(1-\varphi) - \mu\big) - h(\varphi) z,$$

$$\tau\,\partial_t\varphi - \Delta\varphi + \xi + F_2'(\varphi) = \mu + \chi\sigma, \qquad \xi \in \partial F_1(\varphi),$$

$$\partial_t\sigma - \Delta\sigma = -\chi\Delta\varphi - P(\varphi)\big(\sigma + \chi(1-\varphi) - \mu\big) + u,$$

with homogeneous Neumann conditions and initial data, where $F = F_1 + F_2$ is a double-well potential with convex part $F_1$ (possibly singular, e.g. logarithmic), $P \ge 0$ a proliferation function, $\chi \ge 0$ the chemotaxis coefficient, $h(\varphi) z$ a cytotoxic drug term with given $z$, and $u$ a nutrient-supply control. For $\alpha > 0$ the term $\alpha\,\partial_{tt}\mu$ is a hyperbolic relaxation of the Cahn–Hilliard-type equation; $\alpha = 0$ gives the parabolic model. Problem (CP$_\alpha$) minimizes

$$\mathcal{J}(\varphi, u) = \frac{b_1}{2}\int_Q |\varphi - \widehat\varphi_Q|^2 + \frac{b_2}{2}\int_\Omega |\varphi(T) - \widehat\varphi_\Omega|^2 + \frac{b_3}{2}\int_Q |u|^2 + \kappa\, \mathcal{G}(u)$$

over box-constrained controls $u \in \mathcal{U}_{ad} = \{\underline u \le u \le \overline u \text{ a.e. in } Q\}$, with $b_1, b_2, \kappa \ge 0$, $b_3 > 0$ and $\mathcal{G}$ convex, continuous and nonnegative (e.g. the sparsity-promoting $\mathcal{G}(u) = \|u\|_{L^1(Q)}$).

**Theorem.** Under the paper's standing assumptions on the data and potentials and with initial data separated from the singularities of $F_1$, let $u^*$ be any optimal control of the parabolic problem (CP$_0$) with state $(\mu^*, \varphi^*, \sigma^*, \xi^*)$, and let $\alpha_n \searrow 0$ in $(0,1]$. For the adapted problems (ACP$_{\alpha_n}$), which minimize

$$\widetilde{\mathcal{J}}(\varphi, u) = \mathcal{J}(\varphi, u) + \tfrac12 \|u - u^*\|^2_{L^2(Q)}$$

subject to the relaxed state system with parameter $\alpha_n$, there exist optimal controls $u_{\alpha_n} \in \mathcal{U}_{ad}$ such that

$$u_{\alpha_n} \to u^* \ \text{ strongly in } L^2(Q), \qquad \lim_{n \to \infty} \widetilde{\mathcal{J}}(\varphi_{\alpha_n}, u_{\alpha_n}) = \mathcal{J}(\varphi^*, u^*),$$

and the associated states converge to $(\mu^*, \varphi^*, \sigma^*, \xi^*)$; in particular $\varphi_{\alpha_n} \to \varphi^*$ strongly in $C^0([0,T]; H^1(\Omega)) \cap C^0(\overline Q)$ and $\alpha_n \mu_{\alpha_n} \to 0$ strongly in $W^{1,\infty}(0,T; L^2(\Omega))$.

## Expansion

Uniform-in-$\alpha$ a priori bounds (with $\sqrt{\alpha}\,\partial_t\mu$ and $\alpha\,\partial_{tt}\mu$ controlled) give compactness of the states as $\alpha \to 0$ along any weakly-star convergent sequence of controls. Without the adaptation one only learns that limits of optimal controls of (CP$_\alpha$) are optimal for (CP$_0$); every optimal control of the limit problem cannot be expected to be reached this way. The quadratic penalty $\tfrac12\|u - u^*\|^2$ singles out the chosen $u^*$: comparing $\widetilde{\mathcal{J}}$ at $u_{\alpha_n}$ with its value at $u^*$ forces the penalty term to vanish in the limit, giving strong convergence. The paper continues with convergence of the adjoint states and of the first-order necessary optimality conditions.

## Sources

- P. Colli, E. Rocca and J. Sprekels, "Asymptotic analysis of an optimal control problem for a phase field tumor growth model with hyperbolic relaxation", arXiv:2610.04380 (2026), Section 1 (problem (CP$_\alpha$) and state system), Section 2 (uniform bounds and convergence of the states), Section 3 (adapted cost functional and Theorem 3.3), <https://doi.org/10.48550/arXiv.2610.04380>.
