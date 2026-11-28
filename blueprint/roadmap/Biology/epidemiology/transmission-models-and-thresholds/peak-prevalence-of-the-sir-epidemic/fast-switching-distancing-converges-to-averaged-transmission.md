# Fast-switching distancing converges to the averaged transmission rate

Let an epidemic model be written as a control-affine system

$$\dot x(t) = f_0(x(t)) + \sum_{i=1}^m \beta_i(t)\, f_i(x(t)),$$

with locally Lipschitz vector fields $f_0, \dots, f_m$ on a compact positively invariant state set and bounded measurable controls (for the SIR model, $x = (S, I, R)$, $f_0(x) = (0, -\gamma x_2, \gamma x_2)$, $f_1(x) = (-x_1 x_2, x_1 x_2, 0)$, and the control $\beta_1(t)$ is the transmission rate set by the distancing policy). Let $\beta(t) = (\beta_1(t), \dots, \beta_m(t))$ be $T$-periodic with average $\bar\beta_i = \frac1T \int_0^T \beta_i(t)\, dt$, and for $\omega > 0$ let $x_\omega$ solve the system with control $\beta(\omega t)$ and a fixed initial state.

**Averaging (Appendix B).** As $\omega \to \infty$ (switching period tending to $0$), $x_\omega \to \bar x$ uniformly on every compact time interval $[0, t_f]$, where $\bar x$ solves the system with the constant control $\bar\beta$. In particular, a periodically relaxed distancing policy switched rapidly behaves like constant distancing at its time-averaged transmission rate.

## Expansion

Two facts combine. First, for control-affine systems the input-to-trajectory map from $L^1$ controls on $[0, t_f]$ (with the weak-$*$ topology on bounded sets) to continuous trajectories (with the uniform topology) is continuous, because the controls enter linearly and the trajectory depends on them only through integrals against continuous functions. Second, the rescaled periodic inputs $\beta(\omega t)$ converge weak-$*$ to their average $\bar\beta$ as $\omega \to \infty$ (Riemann–Lebesgue-type averaging). The same conclusion follows from classical periodic averaging after the time change $s = \omega t$. Linearity in the control is the essential hypothesis: for nonlinear dependence on $\beta$ the limit is the average of the vector field, not the field at the averaged control.

## Sources

- M. Sadeghi, J. M. Greene, E. D. Sontag, "Universal features of epidemic models under social distancing guidelines", Annual Reviews in Control 51 (2021) 426–440, Appendix B, Equations (43)–(45), <https://doi.org/10.1016/j.arcontrol.2021.04.004> (PMC8063609).
