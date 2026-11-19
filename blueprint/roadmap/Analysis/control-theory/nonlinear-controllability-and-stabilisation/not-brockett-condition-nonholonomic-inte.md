# The nonholonomic integrator violates Brockett's condition

No point $(0, 0, \eta)$ with $\eta \ne 0$ is a value of the nonholonomic integrator $f(x, u) = (u_1, u_2, x_1 u_2 - x_2 u_1)$: the first two coordinates force $u = 0$, and then the third vanishes. So even the image of the whole space is not a neighbourhood of $0$, and Brockett's condition fails (Coron, *Control and Nonlinearity*, AMS 2007, Example 11.2, after Brockett 1983). By Brockett's theorem the nonholonomic integrator, although controllable, cannot be locally asymptotically stabilised by continuous stationary feedback laws; it can be globally stabilised by smooth periodic time-varying feedback (Coron, Example 11.16, from Theorem 11.14).

## Background

- [Brockett's condition](brockett-condition.md): the property shown to fail.
- [The nonholonomic integrator](nonholonomic-integrator.md): the system.
