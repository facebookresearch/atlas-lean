# Infinite-horizon optimality of the stabilizing Riccati feedback

Let $A \in \mathbb{R}^{n \times n}$, $B \in \mathbb{R}^{n \times m}$, $C \in \mathbb{R}^{q \times n}$, $Q = C^\top C$, and $R \in \mathbb{R}^{m \times m}$ positive definite. Assume $(A, B)$ is stabilizable and $(C, A)$ is detectable. Let $P \succeq 0$ be the stabilizing solution of $P = \mathcal{R}(P)$ and $K = (R + B^\top P B)^{-1} B^\top P A$, so that $A - BK$ is convergent. For an initial state $x_0$ and an input sequence $u = (u_k)_{k \ge 0}$, let $x_{k+1} = A x_k + B u_k$ and

$$J(x_0, u) = \sum_{k = 0}^{\infty} \big( x_k^\top Q x_k + u_k^\top R u_k \big) \in [0, \infty].$$

1. **Optimality on the finite-cost inputs.** For every input with $J(x_0, u) < \infty$,

    $$J(x_0, u) = x_0^\top P x_0 + \sum_{k = 0}^{\infty} (u_k + K x_k)^\top (R + B^\top P B)(u_k + K x_k),$$

    so $J(x_0, u) \ge x_0^\top P x_0$, with equality if and only if $u_k = -K x_k$ for every $k$.

2. **The feedback attains it.** The feedback input $u_k = -K x_k$ has finite cost, equal to $x_0^\top P x_0$.
3. **Bound by any stabilizing gain.** If $A - BL$ is convergent, the feedback $u_k = -L x_k$ has cost $x_0^\top P_L x_0$, where $P_L = \sum_{k \ge 0} \big((A - BL)^\top\big)^k (Q + L^\top R L)(A - BL)^k$ is the solution of the Stein equation $P_L = (A - BL)^\top P_L (A - BL) + Q + L^\top R L$. The Riccati iterates from zero satisfy $M_N \preceq P_L$ for every $N$, and their limit satisfies $P \preceq P_L$.

**Proof.**

- **Part 1.** Since $P = \mathcal{R}(P)$, completion of squares gives, for every $k$,

    $$x_k^\top Q x_k + u_k^\top R u_k + x_{k+1}^\top P x_{k+1} - x_k^\top P x_k = (u_k + K x_k)^\top (R + B^\top P B)(u_k + K x_k).$$

    Summing over $k < N$ gives the identity with the boundary term $-x_N^\top P x_N$. Finite cost and detectability give $x_N \to 0$, so the boundary term vanishes as $N \to \infty$.

- **Part 2.** Under $u = -Kx$ the state decays geometrically, so the cost is finite, and part 1 gives the value.
- **Part 3.** The cost of $u = -Lx$ is the Stein series. For each $N$, $x_0^\top M_N x_0$ is the least $N$-step cost with zero terminal cost, which is at most the $N$-step cost of $u = -Lx$, which in turn is at most $x_0^\top P_L x_0$.

## Depends on

- [The Riccati recursion converges to the stabilizing solution](riccati-recursion-converges-to-the-stabilizing-solution.md): the stabilizing solution $P$ and the gain $K$
- [Riccati update](riccati-map.md): the Riccati update $\mathcal{R}$

## Proof depends on

- [Completion of squares in the control](bellman-cost-eq-add.md): the per-step completion of squares
- [The Bellman cost of the linear control](bellman-cost-neg-gain.md): the Bellman cost at $u = -Kx$ is $x^\top \mathcal{R}(P) x = x^\top P x$
- [Vanishing forcing of a stable system, and finite cost under detectability](../../../../Analysis/control-theory/observability-of-linear-systems/finite-cost-implies-state-convergence-under-detectability.md): finite cost and detectability give $x_k \to 0$
- [The Stein equation: series solution and uniqueness](../../../../Analysis/ordinary-differential-equations/stability-of-linear-systems/stein-equation-series-solution-and-uniqueness.md): the cost of a stabilizing feedback as the Stein series
- [Every control sequence costs at least the Riccati value](lqr-cost-ge.md): the Riccati value is a lower bound on every $N$-step cost

## Sources

- E. D. Sontag, *Mathematical Control Theory: Deterministic Finite Dimensional Systems*, 2nd ed., Texts in Applied Mathematics 6, Springer, 1998, <http://www.sontaglab.org/FTPDIR/sontag_mathematical_control_theory_springer98.pdf>, Section 8.4: the infinite-time problem, the bound $x^\top \Pi(\tau) x \le J_\infty(x, \omega)$ (8.56), the completion-of-squares argument for optimality and uniqueness (pp. 382–384), Theorem 41 (p. 384), and Lemma/Exercise 8.4.4, the discrete-time problem with the DARE under controllability (p. 385). These are stated for controllable systems, Theorem 41 in continuous time and Lemma/Exercise 8.4.4 as an exercise in discrete time; the discrete-time version above under stabilizability and detectability, and the bound by a stabilizing gain in part 3, are derived on the page.
