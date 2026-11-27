# Controllability Gramian

For $\dot x = A x + B u$ on finite-dimensional real inner product spaces $E$ (state) and $U$ (control) and $T \in \mathbb{R}$, the **controllability Gramian** is the operator

$$W_T = \int_0^T e^{sA} B B^* e^{sA^*} \, ds : E \to E,$$

where $B^*$ and $e^{sA^*} = (e^{sA})^*$ are adjoints. It is symmetric, and positive semidefinite for $T \ge 0$.

This is Coron, *Control and Nonlinearity* (AMS 2007), Definition 1.10, $C = \int_{T_0}^{T_1} R(T_1, \tau) B B^\top R(T_1, \tau)^\top \, d\tau$, for a time-invariant system, where the resolvent is $R(T_1, \tau) = e^{(T_1 - \tau) A}$, after the change of variables $s = T_1 - \tau$ and with $[T_0, T_1] = [0, T]$. Sontag (*Mathematical Control Theory*, 2nd ed., Section 3.5) uses the same matrix.

## Background

- [One-parameter groups of matrices](../../ordinary-differential-equations/one-parameter-groups-of-matrices/README.md): the semigroup $s \mapsto e^{sA}$ that propagates the control's effect to the final time.
- [Positive-definite matrices](../../../LinearAlgebra/positive-definite-matrices/README.md): for $T \ge 0$ the Gramian is positive semidefinite, and for $T > 0$ it is positive definite exactly when the system is controllable on $[0, T]$.
