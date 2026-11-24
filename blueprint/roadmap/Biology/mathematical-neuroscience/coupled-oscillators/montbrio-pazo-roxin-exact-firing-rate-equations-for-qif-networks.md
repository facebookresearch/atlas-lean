# Exact firing-rate equations for networks of quadratic integrate-and-fire neurons

Consider $N$ globally coupled quadratic integrate-and-fire neurons $\dot V_j = V_j^2 + \eta_j + J r(t) + I(t)$, in units where time and voltage are rescaled to absorb the coefficients, with reset from $V_p$ to $V_r$ in the limit $V_p = -V_r \to \infty$, where $r$ is the population firing rate (fast synapses), $I$ a common input, and the excitabilities $\eta_j$ are drawn from a Lorentzian density with centre $\bar\eta$ and half-width $\Delta$. Montbrió, Pazó and Roxin (2015) show that, in the limit $N \to \infty$, the continuity equation for the density of membrane potentials conditioned on $\eta$ is solved exactly by Lorentzian conditional densities (the Lorentzian ansatz), and that on this family the firing rate $r$ and the mean membrane potential $v$ satisfy exactly the two ordinary differential equations

$$\dot r = \frac{\Delta}{\pi} + 2 r v, \qquad \dot v = v^2 + \bar\eta + J r + I(t) - \pi^2 r^2$$

(equations (12a) and (12b) of the source), obtained by evaluating the conditional centre and half-width at the pole $\eta = \bar\eta - i\Delta$ of the Lorentzian density: $\pi r + i v = w(\bar\eta - i\Delta, t)$.

## Expansion

1. The model: the quadratic integrate-and-fire neuron with reset at infinity, the network coupling through the firing rate, and the continuity equation for the conditional voltage density.
2. The Lorentzian ansatz with half-width $x(\eta, t) = \pi r(\eta, t)$ and centre $y(\eta, t)$, and the complex equation $\partial_t w = i(\eta + J r + I - w^2)$ for $w = x + i y$.
3. The identifications of $r$ and $v$ by contour integration against the Lorentzian density, giving the two equations.
4. The correspondence of the Lorentzian ansatz with the Ott–Antonsen ansatz for phase oscillators by a conformal map, and the attraction of solutions to the Lorentzian family, as separate statements.
5. The steady states and the bistability region of the firing-rate equations, as separate statements.

## Sources

- E. Montbrió, D. Pazó and A. Roxin, Macroscopic description for networks of spiking neurons, Phys. Rev. X 5 (2015), 021028, equations (1), (4)–(12). <https://arxiv.org/abs/1506.06581>
