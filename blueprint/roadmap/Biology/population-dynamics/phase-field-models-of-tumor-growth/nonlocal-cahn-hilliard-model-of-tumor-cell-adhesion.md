# Nonlocal Cahn–Hilliard model of tumor cell adhesion

Let $\Omega \subset \mathbb{R}^d$ be a bounded domain, $\varphi_T$ the tumor volume fraction and $\varphi_\sigma$ the nutrient concentration. Long-range cell-to-cell adhesion is modelled by an integrable convolution kernel $J: \mathbb{R}^d \to \mathbb{R}$ that is even, $J(-x) = J(x)$, and attractive, $J \ge 0$ with $J \not\equiv 0$, and that replaces the gradient term of the [Cahn–Hilliard energy](cahn-hilliard-model-of-tumor-growth.md). With a double-well potential $\Psi$, nutrient diffusivity $D_\sigma > 0$ and chemotaxis parameter $\chi_c > 0$, the free energy is

$$E(\varphi_T, \varphi_\sigma) = \int_\Omega \left(\Psi(\varphi_T) + \frac{D_\sigma}{2}\varphi_\sigma^2 - \chi_c \varphi_T \varphi_\sigma\right) dx + \frac14 \int_\Omega\int_\Omega J(x-y)\big(\varphi_T(x) - \varphi_T(y)\big)^2\, dy\, dx.$$

Its variational derivatives are

$$\mu_T = \frac{\delta E}{\delta \varphi_T} = \Psi'(\varphi_T) - \chi_c\varphi_\sigma + \varphi_T\,(J * 1) - J * \varphi_T, \qquad \mu_\sigma = \frac{\delta E}{\delta\varphi_\sigma} = D_\sigma\varphi_\sigma - \chi_c\varphi_T,$$

where $(J * u)(x) = \int_\Omega J(x-y)u(y)\, dy$. The two hypotheses on $J$ play different roles: evenness is what the first variation uses, while $J \ge 0$ makes the pair term nonnegative, so that unlike values of $\varphi_T$ at nearby points raise the energy, which is the adhesion interpretation. An even kernel of the other sign, such as $J(z) = -e^{-|z|^2}$, gives the same formula for $\mu_T$ but lowers the energy of unlike pairs. With a velocity field $v$, mobilities $M_T, M_\sigma > 0$ and reaction terms $S_T, S_\sigma$, the nonlocal model is

$$\partial_t\varphi_T + \operatorname{div}(\varphi_T v) = \operatorname{div}\big(M_T\varphi_T^2(1-\varphi_T)^2\nabla\mu_T\big) + S_T(\varphi_T, \varphi_\sigma),$$

$$\partial_t\varphi_\sigma + \operatorname{div}(\varphi_\sigma v) = \operatorname{div}\big(M_\sigma\nabla\mu_\sigma\big) + S_\sigma(\varphi_T, \varphi_\sigma).$$

The equation for $\varphi_T$ is second order in space instead of fourth order, and a suitable sequence of kernels concentrating at the origin recovers the local Ginzburg–Landau energy.

## Depends on

- [Cahn–Hilliard model of tumor growth](cahn-hilliard-model-of-tumor-growth.md)

## Proof depends on

- [Fubini's theorem for iterated integrals](../../../MeasureTheory/integration/iterated-integrals/integral-integral-swap.md)

## Expansion

For the nonlocal term, perturb $\varphi_T$ by $s\eta$ and differentiate at $s = 0$: $\frac14\int\int J(x-y)\, 2(\varphi_T(x) - \varphi_T(y))(\eta(x) - \eta(y))\, dy\, dx$. Exchanging $x$ and $y$ in the part with $\eta(y)$ and using $J(-z) = J(z)$ gives $\int_\Omega \eta(x)\int_\Omega J(x-y)(\varphi_T(x) - \varphi_T(y))\, dy\, dx$, so the derivative is $\varphi_T(J*1) - J*\varphi_T$. The local terms give $\Psi'(\varphi_T) - \chi_c\varphi_\sigma$ and $D_\sigma\varphi_\sigma - \chi_c\varphi_T$. The interaction energy is the Helmholtz free energy obtained from microscopic statistical mechanics of phase separation; with $J \ge 0$ the pair energy is lowest when nearby points are in the same phase, which encodes the preferential adhesion of tumor cells to tumor cells, and the cross term $-\chi_c\varphi_T\varphi_\sigma$ produces chemotaxis up the nutrient gradient through $\nabla\mu_T$.

## Sources

- M. Fritz, Tumor evolution models of phase-field type with nonlocal effects and angiogenesis, *Bull. Math. Biol.* 85 (2023), 44, <https://doi.org/10.1007/s11538-023-01151-6> (Section 2.4.1, Equation 2.10).
