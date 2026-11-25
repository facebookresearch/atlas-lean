# Steady-state step response of a stable linear system

Let $A \in \mathbb{R}^{n \times n}$ be Hurwitz, let $B \in \mathbb{R}^{n \times m}$, $C \in \mathbb{R}^{p \times n}$ and $D \in \mathbb{R}^{p \times m}$, and let $u \in \mathbb{R}^m$ be a constant input. Then for every initial state $x_0$ the solution of $\dot x = A x + B u$, $x(0) = x_0$, is

$$x(t) = e^{tA}\bigl(x_0 + A^{-1} B u\bigr) - A^{-1} B u ,$$

and the output $y = C x + D u$ converges as $t \to \infty$:

$$y(t) \to \bigl(D - C A^{-1} B\bigr) u = W(0)\, u ,$$

where $W(s) = C (sI - A)^{-1} B + D$ is the transfer matrix. The matrix $W(0)$ is the **dc gain**.

$A$ is invertible because $0$ is not an eigenvalue. The displayed $x$ satisfies $x(0) = x_0$ and $\dot x = A e^{tA}(x_0 + A^{-1} B u) = A x + B u$, so it is the solution, by uniqueness. The term $e^{tA}(x_0 + A^{-1} B u)$ tends to $0$ because $A$ is Hurwitz.

## Proof depends on

- [Exponential stability of linear differential equations](../ordinary-differential-equations/stability-of-linear-systems/asymptotic-stability-linear-differential-equations.md): the flow of a Hurwitz matrix tends to $0$

- [Duhamel's formula (variation of constants)](../ordinary-differential-equations/duhamel-variation-of-constants.md): the solution of the forced linear equation with constant forcing

## Sources

- E. D. Sontag, *Mathematical Control Theory: Deterministic Finite Dimensional Systems*, 2nd ed., Texts in Applied Mathematics 6, Springer, 1998, <http://www.sontaglab.org/FTPDIR/sontag_mathematical_control_theory_springer98.pdf>, Section 7.4, Exercise 7.4.4 (p. 334): for a single-input single-output uniformly BIBO-stable behavior the output to the constant input $u \equiv 1$ converges to $W(0)$, the dc gain; internal stability implies uniform BIBO stability by Proposition 7.3.3 (p. 328).
