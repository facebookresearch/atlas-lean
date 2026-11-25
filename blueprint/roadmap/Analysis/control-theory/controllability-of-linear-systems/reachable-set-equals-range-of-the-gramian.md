# The reachable set from zero is the range of the controllability Gramian

Let $A : \mathbb{R} \to \mathbb{R}^{n \times n}$ and $B : \mathbb{R} \to \mathbb{R}^{n \times m}$ be continuous, let $\Phi(t, s)$ be the transition matrix of $\dot x = A(t) x$, let $t_0 < t_1$, and let

$$W(t_0, t_1) = \int_{t_0}^{t_1} \Phi(t_1, s) B(s) B(s)^\top \Phi(t_1, s)^\top \, ds$$

be the controllability Gramian. For a continuous control, use the classical solution. For a square-integrable control (modulo equality almost everywhere), use the unique absolutely continuous solution satisfying $\dot x=A(t)x+B(t)u$ almost everywhere. In either case the state reached at $t_1$ from $x(t_0) = 0$ is $\int_{t_0}^{t_1} \Phi(t_1, s) B(s) u(s)\, ds$.

1. The set of states reachable at time $t_1$ from $0$ at time $t_0$ with continuous controls equals $\operatorname{range} W(t_0, t_1)$. The same set is obtained with square-integrable controls.
2. If $z = W(t_0, t_1) \eta$, then the continuous control $u(s) = B(s)^\top \Phi(t_1, s)^\top \eta$ steers $0$ at $t_0$ to $z$ at $t_1$.

$W$ need not be invertible here: when it is singular, $\operatorname{range} W$ is a proper subspace and the statement describes exactly which states are reachable. When $W$ is positive definite, the range is all of $\mathbb{R}^n$ and the system is controllable on $[t_0, t_1]$.

For $u\in L^2$ the forcing $B(\cdot)u$ is integrable on the compact interval. The variation-of-constants integral defines an absolutely continuous solution: multiplying by $\Phi(t_0,t)$ reduces the equation to the indefinite integral of an integrable function. This also proves uniqueness. Thus the endpoint formula is valid beyond the continuous-input version of the linked theorem.

Write $L u = \int_{t_0}^{t_1} \Phi(t_1, s) B(s) u(s)\, ds$ as a bounded operator from $L^2([t_0, t_1]; \mathbb{R}^m)$ to $\mathbb{R}^n$. Its adjoint is $(L^* \eta)(s) = B(s)^\top \Phi(t_1, s)^\top \eta$ and $W = L L^*$. Because the codomain $\mathbb R^n$ is finite dimensional, the range of $L$ is closed, and $\operatorname{range} L L^* = (\ker L^*)^\perp = \operatorname{range} L$. Hence the $L^2$-reachable set is $\operatorname{range} W$. Part 2 is $L(L^* \eta) = W \eta$, and $L^* \eta$ is continuous. So the continuous-control reachable set lies between $\operatorname{range} W$ and the $L^2$-reachable set, which are equal.

## Depends on

- [Variation of constants for time-varying linear systems](../../ordinary-differential-equations/linear-systems-and-fundamental-matrices/variation-of-parameters-time-varying.md): the transition matrix $\Phi$ and the reached state

## Proof depends on

- [Variation of constants for time-varying linear systems](../../ordinary-differential-equations/linear-systems-and-fundamental-matrices/variation-of-parameters-time-varying.md): the endpoint of a controlled trajectory from $0$

## Background

- [Gramian criterion for controllability of time-varying linear systems](gramian-criterion-time-varying.md): the case $W$ positive definite, with the minimum-norm control

## Sources

- E. D. Sontag, *Mathematical Control Theory: Deterministic Finite Dimensional Systems*, 2nd ed., Texts in Applied Mathematics 6, Springer, 1998, <http://www.sontaglab.org/FTPDIR/sontag_mathematical_control_theory_springer98.pdf>, Section 3.5: Example 3.5.1 (the operator $L\omega = \int k(t)^* \omega(t)\,dt$ on $L^2$ and its adjoint, p. 105), Lemma 3.5.2 ($\operatorname{im} LL^* = (\ker L^*)^\perp = \operatorname{im} L$, p. 106), $W = LL^*$ (3.15), and its application to reachability with $k(t)^* = \Phi(\tau, t) B(t)$ leading to Theorem 5 (pp. 106–109); Appendix C.4, formula (C.26), p. 488, for integrable forcing and the corresponding absolutely continuous solution.
