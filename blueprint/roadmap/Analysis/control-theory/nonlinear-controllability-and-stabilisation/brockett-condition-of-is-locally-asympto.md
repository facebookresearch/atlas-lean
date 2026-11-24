# Brockett's necessary condition for stabilisation

Let $E$ and $U$ be finite-dimensional real normed spaces and $f : E \times U \to E$ of class $C^\infty$ with $f(0, 0) = 0$. If $\dot x = f(x, u)$ is locally asymptotically stabilisable by continuous stationary feedback laws, then the image under $f$ of every neighbourhood of $(0, 0)$ is a neighbourhood of $0$.

This is Brockett's theorem (Brockett 1983), as stated in Coron, *Control and Nonlinearity* (AMS 2007), Theorem 11.1. Coron allows $f$ to be defined and smooth only on an open neighbourhood of $(0, 0)$; the statement here is the case of an everywhere defined smooth $f$. Coron derives it from the stronger index condition (Theorem 11.4): there is a continuous feedback whose closed-loop vector field has index $(-1)^n$ at $0$, and a vector field of nonzero degree on a small ball maps it onto a neighbourhood of $0$. The nonholonomic integrator satisfies the regularity hypotheses, so with this theorem [the failure of Brockett's condition](not-brockett-condition-nonholonomic-inte.md) shows that it cannot be stabilised by continuous stationary feedback.

## Background

- [Stabilisability by continuous stationary feedback](is-locally-asymptotically-stabilizable.md): the hypothesis.
- [Brockett's condition](brockett-condition.md): the conclusion.
- [The nonholonomic integrator violates Brockett's condition](not-brockett-condition-nonholonomic-inte.md): Brockett's own example of a controllable system that the theorem rules out.
