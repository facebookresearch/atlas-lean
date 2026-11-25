# Exact cost decomposition and the unique optimal control of finite-horizon LQR

Let $A \in \mathbb{R}^{n \times n}$, $B \in \mathbb{R}^{n \times m}$, let $Q$ and $Q_f$ be symmetric positive semidefinite and $R$ symmetric positive definite, and for an initial state $x_0$ and controls $u_0, \dots, u_{T-1}$ let $x_{t+1} = A x_t + B u_t$ and

$$J_T(x_0, u) = \sum_{t=0}^{T-1} \big(x_t^\top Q x_t + u_t^\top R u_t\big) + x_T^\top Q_f x_T .$$

Let $M_0 = Q_f$ and $M_{j+1} = \mathcal{R}(M_j)$ be the Riccati cost-to-go matrices, where $\mathcal{R}$ is the [Riccati update](riccati-map.md), $S_j = R + B^\top M_j B$ and $K_j = S_j^{-1} B^\top M_j A$. Then:

1. **Exact decomposition.** For every horizon $T$, initial state $x_0$ and control sequence $u$,

    $$J_T(x_0, u) = x_0^\top M_T x_0 + \sum_{t=0}^{T-1} \big(u_t + K_{T-1-t} x_t\big)^\top S_{T-1-t} \big(u_t + K_{T-1-t} x_t\big).$$

2. **Unique optimizer.** Each $S_j$ is positive definite, so the minimum of $J_T(x_0, \cdot)$ is $x_0^\top M_T x_0$, and it is attained by exactly one control sequence, the feedback $u_t = -K_{T-1-t} x_t$ along its own trajectory.

**Proof.** Every $M_j$ is positive semidefinite and every $S_j$ positive definite, by induction from the positivity of the Riccati update. For part 1, write $V_j(x) = x^\top M_j x$. The completion of squares gives, for each $t$ with $j = T - 1 - t$,

$$x_t^\top Q x_t + u_t^\top R u_t + V_j(x_{t+1}) = V_{j+1}(x_t) + (u_t + K_j x_t)^\top S_j (u_t + K_j x_t).$$

Summing over $t < T$, the terms $V_j(x_{t+1})$ for $t < T - 1$ cancel against $V_{j+1}(x_{t+1})$, and $V_0(x_T) = x_T^\top Q_f x_T$, which gives the identity. For part 2, the sum is nonnegative and vanishes exactly when $u_t = -K_{T-1-t} x_t$ for every $t$; given $x_0$ these equations determine $u_0, x_1, u_1, \dots$ recursively, so the minimizing sequence is unique.

## Depends on

- [Riccati update](riccati-map.md)

## Proof depends on

- [Completion of squares in the control](bellman-cost-eq-add.md): the one-step identity with $S = R + B^\top M B$
- [The Bellman cost of the linear control](bellman-cost-neg-gain.md): $\mathcal{B}_M(x, -Kx) = x^\top \mathcal{R}(M) x$
- [The Riccati update preserves positive semidefiniteness](riccati-map-pos-semidef.md): $M_j \succeq 0$ and $S_j \succ 0$ along the recursion

## Background

- [Every control sequence costs at least the Riccati value](lqr-cost-ge.md): the inequality $x_0^\top M_T x_0 \le J_T(x_0, u)$, which part 1 refines to an identity

## Sources

- E. D. Sontag, *Mathematical Control Theory: Deterministic Finite Dimensional Systems*, 2nd ed., Texts in Applied Mathematics 6, Springer, 1998, <http://www.sontaglab.org/FTPDIR/sontag_mathematical_control_theory_springer98.pdf>, Section 8.2: Theorem 37 and Lemma 8.2.1 (pp. 364–365), the continuous-time finite-horizon problem, where the Riccati feedback gives the unique optimal control and the value $x^\top P(t) x$, and Exercise 8.2.7 (p. 369), the discrete-time analogue with a Riccati difference equation, posed as an exercise. The discrete-time decomposition and uniqueness are proved on the page.
