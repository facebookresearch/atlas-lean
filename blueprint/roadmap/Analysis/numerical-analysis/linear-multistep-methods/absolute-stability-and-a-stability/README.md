# Absolute stability and A-stability

Applied to the model problem $y' = \lambda y$, a linear multistep method becomes a linear recurrence whose stability polynomial $\pi(z; \bar h) = \rho(z) - \bar h \sigma(z)$, $\bar h = h\lambda$, decides whether the computed values decay. A method is A-stable when they decay for every step whenever $\operatorname{Re} \lambda < 0$; Dahlquist's second barrier limits A-stable linear multistep methods to order $2$, the trapezium rule being the most accurate of them.

- [Absolute stability of a linear multistep method](absolute-stability.md)
- [Consistent zero-stable methods are absolutely unstable for small positive steps](absolute-instability-for-small-positive-steps.md)
- [A-stability](a-stability.md)
- [The implicit Euler method is A-stable](implicit-euler-is-a-stable.md)
- [No explicit consistent linear multistep method is A-stable](no-explicit-a-stable-linear-multistep-method.md)
- [Second Dahlquist barrier](second-dahlquist-barrier.md)
- [The trapezium rule is the most accurate second-order A-stable method](trapezium-rule-is-the-optimal-a-stable-method.md)

## Related topics

- [Linear multistep methods](../README.md)
- [Stability function of the classical RK4 method](../../runge-kutta-methods/rk4-stability.md): the corresponding notion for a Runge–Kutta method.
