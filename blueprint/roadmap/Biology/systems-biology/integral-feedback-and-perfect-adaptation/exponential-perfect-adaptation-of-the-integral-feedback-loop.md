# Exponential perfect adaptation of the integral-feedback loop

Let $a, b > 0$, let $r$ be constant, and let $(e, z)$ solve $\dot e = -a e - b z + r$, $\dot z = e$ from any initial state. Then:

1. the matrix $A = \begin{bmatrix} -a & -b \\ 1 & 0 \end{bmatrix}$ is Hurwitz, since $\operatorname{tr} A = -a < 0 < b = \det A$;
2. the shifted state $\eta = (e, z - r/b)$ satisfies $\dot\eta = A\eta$, so there are $M, c > 0$, independent of $r$ and of the initial state, with $\|\eta(t)\| \le M e^{-ct}\|\eta(0)\|$;
3. consequently $e(t) \to 0$ and $z(t) \to r/b$ exponentially fast: the output returns to zero after any constant input, which is **perfect adaptation**.

The conclusion holds for all $a, b > 0$; nothing needs to be tuned to the value of $r$.

**Proof.** Part 1 is the trace–determinant criterion for $2 \times 2$ real matrices. For part 2, $\dot\eta = (-a e - b(z - r/b),\ e) = A\eta$, and a Hurwitz matrix gives a uniform exponential bound on $e^{tA}$. Part 3 reads off the two coordinates of $\eta$.

## Depends on

- [The integral-feedback loop as a linear system and its equilibrium](the-integral-feedback-loop-as-a-linear-system-and-its-equilibrium.md): the matrix $A$ and the equilibrium $(0, r/b)$

## Proof depends on

- [Routh–Hurwitz: a real 2 × 2 matrix is Hurwitz iff tr M < 0 < det M](../../../Analysis/ordinary-differential-equations/linear-systems-and-fundamental-matrices/is-hurwitz-iff-trace-neg-and-det-pos.md): the trace–determinant test
- [Exponential stability of linear differential equations](../../../Analysis/ordinary-differential-equations/stability-of-linear-systems/asymptotic-stability-linear-differential-equations.md): a Hurwitz matrix gives exponential decay

## Background

- [Integral feedback gives robust perfect adaptation](output-eq-zero-of-integral-feedback.md): the general robustness statement

## Sources

- K. J. Åström and R. M. Murray, *Feedback Systems: An Introduction for Scientists and Engineers*, 2nd ed., Princeton University Press, 2021, <https://fbswiki.org/>, Section 7.4, integral action (7.26)–(7.27): when the closed loop with integral feedback is stable, the output settles to its reference independently of the plant parameters (pp. 7-25–7-26). The explicit stability and convergence argument for this loop is given on the page.
