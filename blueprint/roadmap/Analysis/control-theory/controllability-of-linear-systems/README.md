# Controllability of linear systems

A linear control system $\dot x = A x + B u$, with state $x(t) \in \mathbb{R}^n$ and control $u(t) \in \mathbb{R}^m$, is controllable on $[0, T]$, for $T > 0$, if every state can be steered to every other state in time $T$. Kalman, Ho and Narendra (1963) characterised this in two ways, which are the first theorems of Coron's *Control and Nonlinearity* (AMS 2007, Chapter 1) and of Sontag's *Mathematical Control Theory* (2nd ed., 1998, Chapter 3). The integral criterion: the system is controllable if and only if the **controllability Gramian** $W_T = \int_0^T e^{sA} B B^\top e^{sA^\top} \, ds$ is invertible, and then the control $u(t) = B^\top e^{(T-t)A^\top} W_T^{-1} (x_1 - e^{TA} x_0)$ steers $x_0$ to $x_1$. The algebraic criterion: the system is controllable if and only if the **Kalman rank condition** $\operatorname{rank} [B, AB, \dots, A^{n-1}B] = n$ holds; in particular controllability does not depend on $T > 0$. The **Hautus test** restates the rank condition through eigenvectors: no complex left eigenvector of $A$ is annihilated by $B$, that is, $\operatorname{rank} [\lambda I - A, B] = n$ for every $\lambda \in \mathbb{C}$.

The pages below state all three criteria for time-invariant systems on finite-dimensional real inner product spaces, with continuous controls (Coron uses $L^\infty$ controls; the notions agree, since an $L^\infty$-controllable system has an invertible Gramian by Coron's Theorem 1.11 and the Gramian criterion then gives continuous controls, compare Coron's Remark 1.3, which treats $L^2$ and $L^1$). The Hautus test is stated for systems given by real matrices. Further pages below treat time-varying and discrete-time systems; [observability and its discrete-time duality](../observability-of-linear-systems/README.md) are treated separately. The Hilbert Uniqueness Method of J.-L. Lions (Coron Section 1.4) lies beyond these pages.

- [Controllability of a linear control system](is-controllable-on.md)
- [Controllability Gramian](gramian.md)
- [Quadratic form of the Gramian](inner-gramian-apply.md)
- [Gramian criterion for controllability](is-controllable-on-iff-bijective-gramian.md)
- [Kalman subspace](kalman-subspace.md)
- [Kalman rank condition, dual form](kalman-subspace-eq-top-iff.md)
- [Kalman rank condition](is-controllable-on-iff-kalman.md)
- [Kalman condition and Hautus test for real matrices](kalman-matrix-iff-hautus.md)
- [Hautus test for controllability](is-controllable-on-iff-hautus.md)

## Time-varying and discrete-time systems

- [Gramian criterion for controllability of time-varying linear systems](gramian-criterion-time-varying.md)
- [The reachable set from zero is the range of the controllability Gramian](reachable-set-equals-range-of-the-gramian.md)
- [Reachability and null-controllability of discrete-time linear systems](kalman-rank-condition-discrete-time.md)

## Related topics

- [Pole placement](../pole-placement/README.md): controllability is exactly what allows a linear state feedback to place the closed-loop eigenvalues anywhere.
- [Nonlinear controllability and stabilisation](../nonlinear-controllability-and-stabilisation/README.md): the Kalman condition is the linear test for small-time local controllability of nonlinear systems, and the Lie algebra rank condition is its nonlinear analogue.
- [Duhamel's formula](../../ordinary-differential-equations/duhamel-variation-of-constants.md): the variation of constants formula that expresses the endpoint of a trajectory in terms of the control.
- [Linear systems and fundamental matrices](../../ordinary-differential-equations/linear-systems-and-fundamental-matrices/README.md): the resolvent $R(t, \tau)$ of a time-varying system, which replaces $e^{(t - \tau) A}$ in Coron's Gramian for time-varying systems.
- [Linear quadratic regulator](../../../ComputerScience/machine-learning/reinforcement-learning/linear-quadratic-regulator/README.md): the Gramian is the matrix of the minimum-energy control problem, the simplest linear-quadratic optimal control problem.
- [Kalman filter](../../../ComputerScience/machine-learning/probabilistic-graphical-models/kalman-filter/README.md): the estimation problem dual to control; its observability condition is the Kalman rank condition for the transposed pair.
