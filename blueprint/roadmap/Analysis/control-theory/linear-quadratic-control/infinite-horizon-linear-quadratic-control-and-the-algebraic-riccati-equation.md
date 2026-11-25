# Infinite-horizon linear-quadratic control and the algebraic Riccati equation

Let $\dot x = Ax + Bu$ with $A \in \mathbb{R}^{n \times n}$, $B \in \mathbb{R}^{n \times m}$, and let $R \in \mathbb{R}^{m \times m}$ be symmetric positive definite and $Q \in \mathbb{R}^{n \times n}$ symmetric positive semidefinite. For an initial state $x$ and a locally integrable control $\omega$ on $[0, \infty)$ with trajectory $\xi$, $\xi(0) = x$, let

$$J_\infty(x, \omega) = \int_0^\infty \big(\omega(t)^\top R\,\omega(t) + \xi(t)^\top Q\,\xi(t)\big)\, dt \in [0, \infty].$$

Let $\Pi(t)$ be the solution on $[0, \infty)$ of $\dot\Pi = -\Pi B R^{-1} B^\top \Pi + \Pi A + A^\top \Pi + Q$, $\Pi(0) = 0$. Assume $(A, B)$ is controllable. Then:

1. **Limit and Riccati equation.** $\Pi(t)$ is nondecreasing in the positive semidefinite order, the limit $\Pi = \lim_{t \to \infty} \Pi(t)$ exists, is symmetric positive semidefinite, and solves the algebraic Riccati equation $\Pi B R^{-1} B^\top \Pi - \Pi A - A^\top \Pi - Q = 0$.
2. **Optimal control.** For every $x$, the minimum of $J_\infty(x, \cdot)$ is $x^\top \Pi x$, and it is attained by the closed-loop control of the constant feedback $u = Fx$ with $F = -R^{-1} B^\top \Pi$; every minimizing control agrees with it almost everywhere. (Changing a control on a null set changes neither the trajectory nor the cost, so uniqueness holds only up to equality almost everywhere.)
3. **Stability.** If moreover $Q$ is positive definite, then $\Pi$ is positive definite and $A + BF$ is Hurwitz: every solution of $\dot\xi = (A + BF)\xi$ tends to $0$.

Controllability is used only to make $J_\infty(x, \cdot)$ finite for some control; without it the limit in part 1 can be infinite. With $Q$ only semidefinite, the optimal feedback need not stabilize: for $Q = 0$ the optimal control is $u = 0$.

**Proof sketch.** By time invariance $x^\top \Pi(\tau) x$ is the optimal cost of the same problem on $[0, \tau]$, which is nondecreasing in $\tau$. Steering $x$ to $0$ in unit time and then applying $u = 0$ gives a finite cost, which bounds $x^\top \Pi(\tau) x$ uniformly in $\tau$; a monotone bounded family of symmetric matrices converges, and passing to the limit in the differential equation gives the algebraic equation. Along any trajectory, the algebraic equation gives the completion of squares $\omega^\top R\,\omega + \xi^\top Q\,\xi = -\tfrac{d}{dt}(\xi^\top \Pi \xi) + (\omega - F\xi)^\top R\,(\omega - F\xi)$. For the feedback control the second term vanishes, which bounds its cost by $x^\top \Pi x$; comparison with the finite-horizon costs, bounded below by $x^\top \Pi(\tau) x$, gives optimality and $\xi(t)^\top \Pi\,\xi(t) \to 0$, and $R \succ 0$ gives uniqueness up to equality almost everywhere: if $\omega \ne F\xi$ on a set of positive measure, integrating the completion of squares gives a $\tau > 0$ with $x^\top \Pi x < \int_0^\tau (\omega^\top R\,\omega + \xi^\top Q\,\xi)\, dt + \xi(\tau)^\top \Pi\,\xi(\tau)$, and since $\xi(\tau)^\top \Pi\,\xi(\tau)$ is the optimal cost from $\xi(\tau)$, time invariance gives $J_\infty(x, \omega) > x^\top \Pi x$. If $Q \succ 0$, then $x^\top \Pi(t) x > 0$ for small $t > 0$ because its derivative at $0$ is $x^\top Q x$, so $\Pi \succ 0$, and $\xi^\top \Pi \xi \to 0$ forces $\xi \to 0$ for every solution of the closed loop.

## Depends on

- [Kalman rank condition](../controllability-of-linear-systems/is-controllable-on-iff-kalman.md): controllability of $(A, B)$ means controllability on $[0, 1]$, so every state can be steered to zero in unit time, which gives a finite cost

## Background

- [First variation and sufficiency for the finite-horizon linear-quadratic problem](first-variation-and-sufficiency-for-the-finite-horizon-linear-quadratic-problem.md): the finite-horizon problem whose optimal costs increase to $x^\top \Pi x$

## Sources

- E. D. Sontag, *Mathematical Control Theory: Deterministic Finite Dimensional Systems*, 2nd ed., Texts in Applied Mathematics 6, Springer, 1998, <http://www.sontaglab.org/FTPDIR/sontag_mathematical_control_theory_springer98.pdf>, Section 8.4: the infinite-time problem (8.53) with $R > 0$, $Q \ge 0$ (p. 380), the Riccati equation (8.54) with $\Pi(0) = 0$ and the monotonicity (8.55) (p. 381), Lemma 8.4.1 (under controllability the limit $\Pi$ exists and solves (ARE), pp. 381–382), and Theorem 41 (the unique optimal control is the feedback $F = -R^{-1}B'\Pi$; if $Q > 0$ then $\Pi > 0$ and closed-loop solutions tend to zero, p. 384). The completion-of-squares identity and the two limiting examples are stated on the page.
