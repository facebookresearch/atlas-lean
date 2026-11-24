# Accelerated gradient methods

Nesterov's accelerated gradient method minimizes a convex function with $L$-Lipschitz gradient at the rate $O(L\|x_0 - x^\star\|^2 / k^2)$, against $O(1/k)$ for plain gradient descent. Wibisono, Wilson and Jordan read acceleration as the discretization of a continuous-time flow: the Euler–Lagrange equation of the Bregman Lagrangian, whose energy is a Lyapunov function giving the rate $O(e^{-\beta_t})$; the polynomial family $\beta_t = p \log t + \log C$ gives $O(1/t^p)$, and $p = 2$ in the Euclidean case is the differential equation $\ddot X + \frac{3}{t}\dot X + \nabla f(X) = 0$ of Su, Boyd and Candès. Wilson, Recht and Jordan discretize the same Lyapunov function to analyse Nesterov's three-sequence method, which couples a gradient step with a dual-averaging (mirror-descent) step.

Nesterov's own analysis uses estimate sequences: quadratic functions $\varphi_k(x) = \varphi_k^* + \frac{\gamma_k}{2}\|x - v_k\|^2$ built from lower models of $f$, with $\varphi_k \le (1 - \lambda_k) f + \lambda_k \varphi_0$ and $f(x_k) \le \varphi_k^*$, so that $f(x_k) - f^* \le \lambda_k(\varphi_0(x^*) - f^*)$. With $\gamma_0 = L$ this gives $L\min\{(1 - \sqrt{\mu/L})^k, 4/(k+2)^2\}\|x_0 - x^*\|^2$ for $\mu$-strongly convex $f$ ($\mu \ge 0$), and with $\gamma_0 = \mu$ the constant-step method with rate $(1 - \sqrt{\mu/L})^k$; both match the lower complexity bounds for first-order methods up to constant factors (in the error for the smooth convex case, in the iteration count for the strongly convex case).

- [Nesterov's $O(1/k^2)$ rate for accelerated gradient descent](nesterov-accelerated-rate.md)
- [One step of the accelerated gradient method does not increase its Lyapunov function](accelerated-lyapunov-step.md)
- [The Lyapunov function of the accelerated gradient method is bounded by its initial value](accelerated-lyapunov-le.md)
- [Energy of the Euclidean Bregman-Lagrangian flow](energy.md)
- [The energy of the Bregman-Lagrangian flow is nonincreasing (Euclidean case)](bregman-lagrangian-energy-antitone-on.md)
- [Convergence rate of the Bregman-Lagrangian flow (Euclidean case)](bregman-lagrangian-rate.md)
- [Polynomial rate $O(1/t^p)$ for the polynomial Bregman-Lagrangian family (Euclidean case)](polynomial-family-rate.md)
- [The Su–Boyd–Candès rate for the continuous limit of Nesterov's method](su-boyd-candes-rate.md)
- [Time dilation of the Bregman-Lagrangian flow (Euclidean case)](time-dilation.md)
- [Time dilation preserves the ideal scaling](time-dilation-ideal-scaling.md)
- [Nesterov's general optimal scheme](is-nesterov-scheme.md)
- [One step of Nesterov's estimate-sequence method contracts its potential](estimate-sequence-step.md)
- [Convergence of Nesterov's estimate-sequence scheme](estimate-sequence-rate.md)
- [Decay of the scaling sequence of Nesterov's scheme](estimate-sequence-lambda-le.md)
- [Optimal rate of Nesterov's scheme started at $\gamma_0 = L$](estimate-sequence-optimal-rate.md)
- [Linear rate of the accelerated gradient method for strongly convex functions](accelerated-strongly-convex-rate.md)

## Related topics

- [Gradient descent](../gradient-descent/README.md): the unaccelerated method, its descent lemma and its $O(1/k)$ rate, on which the accelerated method builds.
- [Mirror descent](../mirror-descent/README.md): the $z$-sequence of the accelerated method is a weighted mirror-descent step; the Bregman Lagrangian is written with the same Bregman divergence.
- [Euler–Lagrange equation](../euler-lagrange-equation/README.md): the variational principle behind the continuous-time flows.
- [Lower complexity bounds for first-order methods](../lower-complexity-bounds-for-first-order-methods/README.md): no method querying only gradients beats these rates by more than a constant factor.
- [Nesterov smoothing](../nesterov-smoothing/README.md): applies the optimal method to a smooth approximation of a nonsmooth max-type function.
