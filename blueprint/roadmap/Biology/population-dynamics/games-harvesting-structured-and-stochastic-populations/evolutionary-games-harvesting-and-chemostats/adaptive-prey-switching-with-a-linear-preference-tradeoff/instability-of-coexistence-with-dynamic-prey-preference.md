# Instability of coexistence when prey preference is a dynamic trait

**Model.** Replace the abrupt diet switch of a 1 predator–2 prey Lotka–Volterra system by a predator trait $q \in [0,1]$, the fraction of predation directed at the preferred prey $p_1$, evolving (by rapid evolution or plasticity) on the same time scale as the populations, toward the diet favored by optimal foraging:

$$
\begin{aligned}
\dot p_1 &= r_1 p_1 - q\, p_1 z, \qquad \dot p_2 = r_2 p_2 - (1 - q)\, p_2 z,\\
\dot z &= e\, q\, p_1 z + e (1 - q) q_2\, p_2 z - m z, \qquad \dot q = q (1 - q)(p_1 - a_q p_2),
\end{aligned}
$$

with $r_1 > r_2 > 0$, $m > 0$, $e \in (0,1)$, $0 < q_2 < 1$ the relative benefit of the defended prey $p_2$, and $a_q > 0$ the slope of the linear preference tradeoff. At $q = 1$ and $q = 0$ the vector field reduces to the two branches of the piecewise-smooth switching model.

**Coexistence state.** The unique interior steady state is

$$
\tilde p_1 = \frac{a_q m (r_1 + r_2)}{e(r_1 a_q + r_2 q_2)}, \qquad \tilde p_2 = \frac{m (r_1 + r_2)}{e(r_1 a_q + r_2 q_2)}, \qquad \tilde z = r_1 + r_2, \qquad \tilde q = \frac{r_1}{r_1 + r_2},
$$

the same densities as the pseudo-equilibrium of the piecewise-smooth model and the $k \to \infty$ limit of the tanh-smoothed model.

**Proposition 2.3.** If $a_q = q_2$, all four eigenvalues of the Jacobian at the coexistence state are purely imaginary.

**Proposition 2.4.** If $a_q \ne q_2$, the coexistence state is linearly unstable.

## Expansion

At the coexistence state the Jacobian has zero trace, and its characteristic polynomial is

$$
\lambda^4 + \frac{m\left(e q_2 r_2^2 + a_q r_1 (e r_1 + 2 r_2)\right)}{e(a_q r_1 + q_2 r_2)}\lambda^2 + \frac{a_q r_1 r_2 m^2 (a_q - q_2)(r_1 - r_2)}{e(a_q r_1 + q_2 r_2)^2}\lambda + \frac{a_q r_1 r_2 m^2 (r_1 + r_2)}{e(a_q r_1 + q_2 r_2)} .
$$

For $a_q = q_2$ the linear term vanishes, and the resulting quadratic in $u = \lambda^2$ has positive discriminant and two negative roots, giving two imaginary pairs. For $a_q \ne q_2$ the linear coefficient is real and nonzero, which is impossible if all roots were purely imaginary (their elementary symmetric function of degree three would be imaginary). So some eigenvalue has nonzero real part, and since the eigenvalues sum to the trace $0$, another has real part of the opposite sign: the state is unstable. Unlike the tanh-smoothed switching model, which has a stable coexistence state for steep tradeoffs, coupling the preference to the population dynamics without time-scale separation destabilizes coexistence and produces oscillations.

## Depends on

- [Stability of coexistence in a smooth prey-switching model](stability-of-coexistence-in-a-smooth-prey-switching-model.md)

## Sources

- Sofia H. Piltz, Lauri Harhanen, Mason A. Porter, Philip K. Maini, "Inferring parameters of prey switching in a 1 predator–2 prey plankton system with a linear preference tradeoff", Journal of Theoretical Biology 456 (2018), 108–122, <https://doi.org/10.1016/j.jtbi.2018.07.005>. Published version of arXiv:1610.07094, cited next; locators there refer to the arXiv version.
- Sofia H. Piltz, Lauri Harhanen, Mason A. Porter, Philip K. Maini, "Inferring parameters of prey switching in a plankton 1 predator–2 prey system with a linear preference tradeoff," arXiv 2016. Section 2.2 (smooth model II), Section 2.3 (coexistence state), Propositions 2.3 and 2.4, Appendix B. <https://doi.org/10.48550/arXiv.1610.07094>
