# The state-transition matrix of a time-varying system is not the exponential of the integral

For a continuous $A : \mathbb{R} \to \mathbb{R}^{n \times n}$ let $\Phi(t, \sigma)$ be the state-transition matrix, the solution of $\partial_t \Phi(t, \sigma) = A(t)\Phi(t, \sigma)$ with $\Phi(\sigma, \sigma) = I$, so that $x(t) = \Phi(t, \sigma)x(\sigma)$ for solutions of $\dot x = A(t)x$.

1. **Commuting case.** If $A(s)A(s') = A(s')A(s)$ for all $s, s' \in [\sigma, t]$, then $\Phi(t, \sigma) = \exp\big(\int_\sigma^t A(s)\, ds\big)$.
2. **Noncommuting witness.** For $A(t) = \begin{bmatrix} 0 & t \\ 0 & 1 \end{bmatrix}$, whose values at different times do not commute,

    $$\Phi(1, 0) = \begin{bmatrix} 1 & 1 \\ 0 & e \end{bmatrix} \ne \begin{bmatrix} 1 & \tfrac{e - 1}{2} \\ 0 & e \end{bmatrix} = \exp\Big(\int_0^1 A(s)\, ds\Big).$$

3. **Order of an ordered product.** For a piecewise-constant system equal to $A_1$ on $[0, 1)$ and to $A_2$ on $[1, 2)$, the transition matrix over $[0, 2]$ is the ordered product $e^{A_2}e^{A_1}$, with the later factor on the left. For $A_1 = \begin{bmatrix} 0 & 1 \\ 0 & 0 \end{bmatrix}$ and $A_2 = \begin{bmatrix} 0 & 0 \\ 1 & 0 \end{bmatrix}$, $e^{A_2}e^{A_1} = \begin{bmatrix} 1 & 1 \\ 1 & 2 \end{bmatrix}$ differs from the reversed product $e^{A_1}e^{A_2} = \begin{bmatrix} 2 & 1 \\ 1 & 1 \end{bmatrix}$.

**Proof.** For part 1, $E(t) = \exp(\int_\sigma^t A)$ satisfies $\dot E = A(t)E$, because $A(t)$ commutes with $\int_\sigma^t A$ and therefore with its powers, so the derivative of each power $(\int_\sigma^t A)^k$ is $kA(t)(\int_\sigma^t A)^{k-1}$; uniqueness of solutions gives $E = \Phi(\cdot, \sigma)$. For part 2, $A(s)A(s') = \begin{bmatrix} 0 & s \\ 0 & 1 \end{bmatrix}$, which depends on the order. Solving $\dot x_2 = x_2$, $\dot x_1 = t x_2$ gives $x_2(t) = e^t x_2(0)$ and $x_1(t) = x_1(0) + (te^t - e^t + 1)x_2(0)$, so $\Phi(1, 0)$ has upper-right entry $1$. On the other side, $N = \int_0^1 A = \begin{bmatrix} 0 & \tfrac12 \\ 0 & 1 \end{bmatrix}$ satisfies $N^k = \begin{bmatrix} 0 & \tfrac12 \\ 0 & 1 \end{bmatrix}$ for $k \ge 1$, so $e^N = I + (e - 1)N$, with upper-right entry $\tfrac{e - 1}{2}$. Part 3 is the composition rule $\Phi(2, 0) = \Phi(2, 1)\Phi(1, 0)$, the nilpotent exponentials $e^{A_1} = I + A_1$ and $e^{A_2} = I + A_2$, and multiplication.

## Background

- [Fundamental matrix of a linear system](fundamental-matrix-linear-system.md): the fundamental matrix of a time-varying linear system

## Sources

- E. D. Sontag, *Mathematical Control Theory: Deterministic Finite Dimensional Systems*, 2nd ed., Texts in Applied Mathematics 6, Springer, 1998, <http://www.sontaglab.org/FTPDIR/sontag_mathematical_control_theory_springer98.pdf>, Appendix C.4: the fundamental solution $\Phi(\tau, \sigma)$ of $\dot X = A(t)X$, $X(\sigma) = I$ (C.24), and its composition and inverse properties (pp. 487–488), with $\Phi(t, \sigma) = e^{(t - \sigma)A}$ for constant $A$. The commuting criterion and the two witnesses are derived on the page.
