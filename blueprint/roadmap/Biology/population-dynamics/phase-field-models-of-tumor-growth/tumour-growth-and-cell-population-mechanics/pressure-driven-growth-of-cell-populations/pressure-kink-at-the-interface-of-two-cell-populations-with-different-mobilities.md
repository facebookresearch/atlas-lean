# Pressure kink at the interface of two cell populations with different mobilities

**Model.** A proliferating population $\rho_1$ and a non-proliferating population $\rho_2$ share the pressure $p = \Pi(\rho_1 + \rho_2)$ and move down its gradient with mobilities $\mu_1, \mu_2 > 0$:

$$\partial_t\rho_1 - \mu_1\operatorname{div}(\rho_1\nabla p) = G(p)\,\rho_1, \qquad \partial_t\rho_2 - \mu_2\operatorname{div}(\rho_2\nabla p) = 0,$$

with $G' < 0$, $G(P) = 0$ for a homeostatic pressure $P > 0$, and $\Pi(0) = 0$, $\Pi' > 0$ on $(0,\infty)$.

**Theorem.** In one space dimension, for every $N_2 > 0$ there exist a speed $c > 0$, a width $\ell > 0$ and componentwise nonnegative profiles $(\rho_1, \rho_2)(z)$, $z = x - ct$, solving

$$-c\,\rho_1' - \mu_1(\rho_1 p')' = G(p)\rho_1, \qquad -c\,\rho_2' - \mu_2(\rho_2 p')' = 0,$$

such that $\rho_1 > 0$ on $(-\infty, 0)$ and $\rho_1 = 0$ on $[0, \infty)$, $\rho_2 > 0$ on $[0, \ell)$ and $\rho_2 = 0$ outside $[0, \ell)$, $\rho_1(z) \to \Pi^{-1}(P)$ as $z \to -\infty$, both $\rho_1$ and $\rho_2$ are nonincreasing where positive, and $\int_0^\ell \rho_2 = N_2$. The pushing population $1$ and the pushed population $2$ stay segregated, and the pressure has a kink at the interface:

$$\operatorname{sgn}\big(p'(0^+) - p'(0^-)\big) = \operatorname{sgn}(\mu_2 - \mu_1).$$

## Expansion

Integrating the $\rho_2$ equation from $z \in [0,\ell]$ to $\infty$ gives $p'(z) = -c/\mu_2$, hence $p(z) = c(\ell - z)/\mu_2$ on $[0,\ell]$; at the trailing side the Darcy velocity of population $1$ must also equal $c$, so $p'(0^-) = -c/\mu_1$. Hence $p'(0^+) - p'(0^-) = c(\mu_2 - \mu_1)/(\mu_1\mu_2)$, and since $p' < 0$ the jump in slope has the sign of $\mu_2 - \mu_1$: a less mobile population ahead produces a steeper pressure drop. Simulations of the individual-based model with $\mu_1 \le \mu_2$ show the same sharp segregation, nonincreasing densities and pressure-slope jump.

## Depends on

- [Travelling waves of pressure-limited cell population growth](travelling-waves-of-pressure-limited-cell-population-growth.md)

## Sources

- M. A. J. Chaplain, T. Lorenzi and F. R. Macfarlane, "Bridging the gap between individual-based and continuum models of growing cell populations", arXiv:1812.05872 (2018), Section 4.1 (travelling-wave problem for two populations and Theorem 2) and Section 4.2 (comparison with the individual-based model), <https://doi.org/10.48550/arXiv.1812.05872>.
