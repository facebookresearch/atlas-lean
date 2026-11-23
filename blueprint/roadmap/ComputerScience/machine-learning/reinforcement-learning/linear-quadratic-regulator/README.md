# Linear quadratic regulator

The linear quadratic regulator (LQR) controls the linear system $x_{t+1} = A x_t + B u_t$ so as to minimize the quadratic cost $\sum_t (x_t^\top Q x_t + u_t^\top R u_t)$. Recht (2019) uses it as the baseline on which to compare reinforcement learning methods: with known dynamics, dynamic programming solves it exactly. The cost-to-go is a quadratic form $x^\top M_t x$, the optimal control is the linear state feedback $u_t = -K_t x_t$, and the matrices are computed backwards by the Riccati recursion, a completion of squares in the control at each step. Here the deterministic version of the source's finite-horizon problem (4.1), with terminal cost, is solved in full, under the added assumption that $R$ is positive definite; the infinite-horizon limit, the discrete algebraic Riccati equation and its stabilizing solution, and the unknown-dynamics problems of the source are not treated here.

- [Riccati gain](riccati-gain.md)
- [Riccati update](riccati-map.md)
- [One-step Bellman cost](bellman-cost.md)
- [Completion of squares in the control](bellman-cost-eq-add.md)
- [The Bellman cost of the linear control](bellman-cost-neg-gain.md)
- [The linear control minimizes the one-step Bellman cost](bellman-cost-ge.md)
- [The Riccati update preserves positive semidefiniteness](riccati-map-pos-semidef.md)
- [Riccati recursion](riccati-cost-to-go.md)
- [States of the linear system](lqr-state.md)
- [Finite-horizon LQR cost](lqr-cost.md)
- [Every control sequence costs at least the Riccati value](lqr-cost-ge.md)
- [The linear feedback attains the Riccati value](lqr-cost-feedback.md)

## Related topics

- [Value iteration](../../../heuristic-search-and-planning/value-iteration/README.md): dynamic programming for finite Markov decision processes; the Riccati recursion is value iteration for quadratic value functions.
- [Optimality of stationary policies](../../../heuristic-search-and-planning/optimality-of-stationary-policies/README.md): the finite-horizon DP algorithm for finite Markov decision processes; the Riccati recursion is its linear-quadratic case.
- [Positive-definite matrices](../../../../LinearAlgebra/positive-definite-matrices/README.md): the positive semidefiniteness that keeps the recursion well defined.
- [Viscosity solutions of Hamilton–Jacobi equations](../../../../Analysis/partial-differential-equations/viscosity-solutions-of-hamilton-jacobi-equations/README.md): in continuous time the dynamic programming equation becomes the Hamilton–Jacobi–Bellman equation, whose value functions are viscosity solutions.
- [Controllability of linear systems](../../../../Analysis/control-theory/controllability-of-linear-systems/README.md): the Kalman rank condition is the classical hypothesis under which the infinite-horizon problem has a stabilising solution, and the controllability Gramian solves the minimum-energy problem.
- [Pole placement](../../../../Analysis/control-theory/pole-placement/README.md): the other classical way to compute a stabilising linear state feedback, by prescribing the closed-loop eigenvalues.
- [Recursive least squares](../../../../Analysis/control-theory/recursive-least-squares/README.md): the estimator whose running estimates are plugged into the Riccati feedback by certainty equivalence.
