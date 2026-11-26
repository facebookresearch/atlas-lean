# Travelling waves of pressure-limited cell population growth

**Model.** Let $\rho(t,x) \ge 0$ be a cell density that moves down gradients of the cell pressure $p = \Pi(\rho)$ (Darcy's law with mobility $\mu > 0$) and grows at a pressure-dependent net rate $G(p)$:

$$\partial_t\rho - \mu\,\operatorname{div}(\rho\nabla p) = G(p)\,\rho.$$

Assume

$$G'(p) < 0, \quad G(P) = 0 \qquad\text{and}\qquad \Pi(0) = 0, \quad \Pi'(\rho) > 0 \ \text{ for } \rho > 0,$$

where $P > 0$ is the homeostatic pressure at which cell death balances division (e.g. $\Pi(\rho) = K_\gamma\rho^\gamma$, $\gamma > 1$). This continuum model arises formally, in the limit of small time and space steps, from an individual-based model in which cells on a lattice divide or die with probabilities set by $G$ at the local pressure and perform a random walk biased down pressure differences: a discrete-time branching random walk.

**Theorem.** In one space dimension there exists a speed $c > 0$ and a nonnegative, nonincreasing profile $\rho(z)$, $z = x - ct$, solving

$$-c\,\rho' - \mu\,(\rho\, p')' = G(p)\,\rho, \qquad p = \Pi(\rho),$$

with $\rho(z) \to \Pi^{-1}(P)$ as $z \to -\infty$ and $\rho(z) \to 0$ as $z \to +\infty$. The invading population is thus a front connecting the homeostatic density behind it to empty space ahead of it.

## Expansion

Writing the equation in terms of $p$ turns it into a degenerate (porous-medium type) reaction–diffusion equation, since the effective diffusivity $\mu\rho\Pi'(\rho)$ vanishes at $\rho = 0$, and the travelling-wave problem reduces to an ODE for the pressure profile connecting the homeostatic pressure $P$ to $0$. Simulations of the individual-based model and of the PDE agree closely on the travelling front; differences appear near sharp transitions from high to low density, where demographic extinction in the stochastic model matters. In the incompressible limit $\gamma \to \infty$ such models converge to Hele-Shaw free-boundary problems.

## Sources

- M. A. J. Chaplain, T. Lorenzi and F. R. Macfarlane, "Bridging the gap between individual-based and continuum models of growing cell populations", arXiv:1812.05872 (2018), Section 2 (individual-based model), Section 3 (formal derivation of the continuum model), Section 4.1 (Theorem 1), <https://doi.org/10.48550/arXiv.1812.05872>.
