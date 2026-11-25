# Pole placement

For a controllable linear system $\dot x = A x + B u$, a linear state feedback $u = K x$ can give the closed-loop matrix $A + BK$ any prescribed characteristic polynomial: this is the **pole-shifting theorem** of Wonham (1967) (Coron, *Control and Nonlinearity*, AMS 2007, Theorem 10.1; Sontag, *Mathematical Control Theory*, 2nd ed., 1998, Theorem 13, which also gives the converse). Choosing the closed-loop eigenvalues in the open left half-plane makes $0$ globally asymptotically stable for $\dot x = (A + BK) x$, so every controllable linear system is stabilisable by linear feedback, and by the linearisation principle every nonlinear system whose linearisation at an equilibrium is controllable is locally stabilisable (Coron, Section 10.2).

Coron proves the single-input case through the controller (companion) form of $(A, b)$ (Lemma 10.2) and reduces several inputs to one with Heymann's lemma (Lemma 10.3, in Hautus's proof). The pages below give the theorem over an arbitrary field. The single-input case uses Ackermann's formula $K = -q \, P(A)$, where $q$ is the linear form equal to $1$ on $A^{n-1} b$ and to $0$ on $b, \dots, A^{n-2} b$, instead of the controller form; Heymann's lemma follows Coron's proof. The stabilisation of controllable linear systems by linear feedback (Coron, Corollary 10.12) follows, with the exponential decay of Hurwitz semigroups from Lyapunov's indirect method. Uniqueness of the feedback for one input (Coron, Remark 10.5), the converse (Sontag, Theorem 13) and the local stabilisation of nonlinear systems with controllable linearisation (Coron, Theorem 10.14) lie beyond these pages.

- [Pole placement for single-input systems](exists-charpoly-add-smul-right-eq.md)
- [Heymann's lemma](exists-span-pow-add-comp-eq-top.md)
- [Pole-shifting theorem](exists-charpoly-add-comp-eq.md)
- [Controllable linear systems have a Hurwitz closed loop](exists-is-hurwitz-add-mul.md)
- [Exponential stabilisation of controllable linear systems](exists-norm-exp-add-mul-le.md)

## Related topics

- [Controllability of linear systems](../controllability-of-linear-systems/README.md): the Kalman rank condition is the hypothesis of pole placement.
- [Lyapunov's indirect method](../../ordinary-differential-equations/lyapunov-s-indirect-method/README.md): a matrix with all eigenvalues in the open left half-plane generates an exponentially stable flow, and stability of the linearisation gives local stability of a nonlinear equilibrium.
- [Linear quadratic regulator](../../../ComputerScience/machine-learning/reinforcement-learning/linear-quadratic-regulator/README.md): the other classical way to compute a stabilising linear feedback, by optimising a quadratic cost through the Riccati equation.
