# Probability current and boundary mass

For a diffusion on $[0, 1]$ with drift $b$ and infinitesimal variance $a$ whose law has an interior density $p(t, x)$ satisfying the forward equation $\partial_tp = \frac12\partial_x^2(ap) - \partial_x(bp)$, define the probability current $J(t, x) = b(x)p(t, x) - \frac12\partial_x(a(x)p(t, x))$. Then the forward equation is the conservation law $\partial_tp = -\partial_xJ$, and integrating over $[c, d] \subset (0, 1)$ gives

$$\frac{d}{dt}\int_c^dp(t, x)\,dx = J(t, c) - J(t, d),$$

so the interior mass changes only through the currents at the ends of the interval. Letting $c \downarrow 0$ and $d \uparrow 1$ where the limits exist, the mass of the fixation atom grows at rate $J(t, 1^-)$ and that of the loss atom at rate $-J(t, 0^+)$. A stationary density with zero current solves $\frac12(a\pi)' = b\pi$, the equilibrium condition of zero flux; Wright's stationary density of the Wright–Fisher diffusion with mutation solves this equation. In the Poisson random field the mutational input enters through the boundary condition $\lim_{x \downarrow 0}xf(x, t) = \theta\rho(t)$ of Evans, Shvets and Slatkin (2007, Section 3), and the stationary Sawyer–Hartl density has the constant nonzero current $\theta\sigma/(1 - e^{-2\sigma})$, the rate at which input is carried through $(0, 1)$ to fixation.

## Depends on

- [Wright's stationary density solves the zero-flux equation](../../../Biology/population-genetics/diffusion-theory/wright-fisher-diffusion/deriv-flux-wright-density.md)
- [Probability current of the Poisson random field density](../../../Biology/population-genetics/diffusion-theory/poisson-random-field-model/current-prf-density.md)
- [Fixation flux and divergence in the Poisson random field](../../../Biology/population-genetics/diffusion-theory/poisson-random-field-model/fixation-flux-and-divergence.md)

## Expansion

1. The current, the conservation form of the forward equation, and interior mass balance on subintervals.
2. The boundary limits of the current and the growth rates of the loss and fixation atoms.
3. Zero-current stationary densities as the reversible stationary solutions.
4. Influx boundary conditions and constant nonzero currents in the Poisson random field.

## Sources

- S. N. Evans, Y. Shvets and M. Slatkin, Non-equilibrium theory of the allele frequency spectrum, Theor. Popul. Biol. 71 (2007), 109–119, abstract and Section 3. <https://doi.org/10.1016/j.tpb.2006.06.005>
- S. Zhao, M. Lascoux, A. D. J. Overall and D. Waxman, The characteristic trajectory of a fixing allele: a consequence of fictitious selection that arises from conditioning, Genetics 195 (2013), 993–1006, Appendix C (the probability current). <https://doi.org/10.1534/genetics.113.156059>
