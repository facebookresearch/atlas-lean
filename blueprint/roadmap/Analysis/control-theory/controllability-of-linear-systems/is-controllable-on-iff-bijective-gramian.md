# Gramian criterion for controllability

Let $T > 0$. The system $\dot x = A x + B u$ on finite-dimensional real inner product spaces is controllable on $[0, T]$ if and only if its controllability Gramian $W_T$ is invertible.

This is Coron, *Control and Nonlinearity* (AMS 2007), Theorem 1.11, which Coron attributes to Kalman, Ho and Narendra (1963, Theorem 5), here for time-invariant systems (Coron treats time-varying systems $\dot x = A(t) x + B(t) u$). If $W_T$ is invertible, the control $u(t) = B^* e^{(T - t)A^*} W_T^{-1} (x_1 - e^{TA} x_0)$ steers $x_0$ to $x_1$ (Coron (1.18)); it is continuous. If $W_T \eta = 0$ with $\eta \ne 0$, the quadratic form shows $B^* e^{sA^*} \eta = 0$ on $[0, T]$, so $\eta$ is orthogonal to the endpoint $\int_0^T e^{(T-s)A} B u(s) \, ds$ of every trajectory from $0$, and $\eta$ cannot be reached.

## Informally uses

- [Duhamel's formula](../../ordinary-differential-equations/duhamel-variation-of-constants.md): the endpoint of a trajectory is $e^{TA} x_0 + \int_0^T e^{(T-s)A} B u(s) \, ds$ (Coron (1.14)).
- [Quadratic form of the Gramian](inner-gramian-apply.md): $W_T \eta = 0$ forces $B^* e^{sA^*} \eta = 0$ for $s \in [0, T]$.
