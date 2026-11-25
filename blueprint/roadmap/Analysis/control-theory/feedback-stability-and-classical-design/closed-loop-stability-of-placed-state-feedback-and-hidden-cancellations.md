# Closed-loop stability of placed state feedback, and hidden cancellations

1. **Placed state feedback is internally stable.** Let $A \in \mathbb{R}^{n \times n}$ and $b \in \mathbb{R}^n$ satisfy the Kalman rank condition. Let $P$ be a monic real polynomial of degree $n$, and $k^\top$ a row vector with $\det(sI - (A - b k^\top)) = P(s)$. If every root of $P$ has negative real part, every solution of $\dot x = (A - b k^\top) x$ decays exponentially. If every root of $P$ has modulus less than $1$, every solution of $x(t+1) = (A - b k^\top) x(t)$ decays geometrically.
2. **Scalar gain range.** For $\dot x = a x + b u$ with $u = -k x$ ($a, b, k \in \mathbb{R}$), the closed loop $\dot x = (a - bk) x$ is exponentially stable if and only if $a - bk < 0$. In discrete time, $x(t+1) = (a - bk) x(t)$ is exponentially stable, that is, its solutions decay geometrically, if and only if $|a - bk| < 1$.
3. **An unstable cancellation stays unstable.** Take the plant $\dot x = x + u$, $y = x$, with transfer function $1/(s - 1)$, and the controller $\dot x_K = -x_K + e$, $u = -2 x_K + e$, with transfer function $(s - 1)/(s + 1)$. Close the loop with $e = r - y$. The loop transfer function is $1/(s + 1)$, and the transfer function from $r$ to $y$ is $1/(s + 2)$. Both have their only pole in the open left half-plane. But the closed-loop state matrix is

    $$A_{cl} = \begin{bmatrix} 0 & -2 \\ -1 & -1 \end{bmatrix},$$

    with characteristic polynomial $s^2 + s - 2 = (s - 1)(s + 2)$, so the full closed loop has the unstable eigenvalue $1$.

4. **A singular loop.** If the plant and controller have direct feedthroughs $D$ and $D_K$ with $I + D D_K$ singular, for instance scalar $D = 1$ and $D_K = -1$, the loop equation $(I + D D_K) y = \dots$ does not determine $y$, so the interconnection is not well posed and does not define a closed-loop state-space system with input $r$.

**Proof.**

- **Part 1.** The roots of $P$ are the eigenvalues of $A - bk^\top$. A Hurwitz (convergent) matrix gives exponentially (geometrically) decaying solutions. Gains $k$ that assign any monic $P$ exist by the pole-shifting theorem.
- **Part 2.** This is the case $n = 1$.
- **Part 3.** Substituting $e = r - x$ gives $\dot x = x + (-2 x_K + r - x) = -2 x_K + r$ and $\dot x_K = -x_K + r - x$. The cancelled factor $s - 1$ of the loop transfer function remains an eigenvalue of the full state matrix.
- **Part 4.** With $D D_K = -1$, the output equation reads $0 \cdot y = C x + D C_K x_K + D D_K r$, which constrains the states instead of determining $y$.

## Depends on

- [Pole-shifting theorem](../pole-placement/exists-charpoly-add-comp-eq.md): state feedback can assign any monic characteristic polynomial to a controllable pair

## Proof depends on

- [Exponential stability of linear differential equations](../../ordinary-differential-equations/stability-of-linear-systems/asymptotic-stability-linear-differential-equations.md): Hurwitz matrices give exponentially decaying solutions
- [Exponential stability of linear difference equations](../../ordinary-differential-equations/stability-of-linear-systems/asymptotic-stability-linear-difference-equations.md): convergent matrices give geometrically decaying solutions

## Background

- [Closed-loop transfer maps of a feedback loop](closed-loop-transfer-maps-of-a-feedback-loop.md): the sensitivity maps of the same feedback loop
- [Exponential stabilisation of controllable linear systems](../pole-placement/exists-norm-exp-add-mul-le.md): the continuous-time existence form of part 1, for one stabilizing gain

## Sources

- E. D. Sontag, *Mathematical Control Theory: Deterministic Finite Dimensional Systems*, 2nd ed., Texts in Applied Mathematics 6, Springer, 1998, <http://www.sontaglab.org/FTPDIR/sontag_mathematical_control_theory_springer98.pdf>, Section 5.5: Theorem 13, the pole-shifting theorem (p. 186).
- K. J. Åström and R. M. Murray, *Feedback Systems: An Introduction for Scientists and Engineers*, 2nd ed., Princeton University Press, 2021 (electronic edition v3.0i, <http://fbsbook.org>), Section 7.2, stabilization and eigenvalue assignment by state feedback (from p. 7-9), and Section 12.1, Example 12.1: with $P = 1/(s - a)$ and $C = k(s - a)/s$ the loop transfer function $k/s$ hides the unstable pole, which appears in another of the Gang of Four (p. 12-5).
