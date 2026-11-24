# Reachability and null-controllability of discrete-time linear systems

Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, let $n \ge 0$ and $m \ge 1$, and let $A \in \mathbb{K}^{n \times n}$ and $B \in \mathbb{K}^{n \times m}$. Consider the discrete-time linear system

$$x(t+1) = A\,x(t) + B\,u(t), \qquad t = 0, 1, 2, \dots,$$

with inputs $u(t) \in \mathbb{K}^m$. For $N \ge 0$ write

$$R_N(A, B) = [\,B,\ AB,\ \dots,\ A^{N-1} B\,] \in \mathbb{K}^{n \times Nm}, \qquad R(A, B) = R_n(A, B);$$

for $N = 0$ this is the empty $n \times 0$ matrix, whose column space is $\{0\}$ and whose rank is $0$.

Starting from $x(0) = x_0$, the state after $N$ steps is

$$x(N) = A^N x_0 + \sum_{j=0}^{N-1} A^{N-1-j} B\, u(j) = A^N x_0 + R_N(A, B)\, \begin{bmatrix} u(N-1) \\ \vdots \\ u(0) \end{bmatrix}.$$

Then:

1. **Reachability in $N$ steps.** The states reachable from $0$ in $N$ steps are exactly the column space of $R_N(A, B)$. Every state can be steered to every state in exactly $N$ steps if and only if $\operatorname{rank} R_N(A, B) = n$; a steering input is obtained from any right inverse of $R_N(A, B)$.
2. **Saturation.** For $N \ge n$ the column space of $R_N(A, B)$ equals that of $R_n(A, B)$.
3. **Kalman rank condition.** The system is controllable (for all states $x, z$ there are $N \ge 0$ and inputs steering $x$ to $z$ in $N$ steps) if and only if $\operatorname{rank} R(A, B) = n$.
4. **Null-controllability in $N$ steps.** Every initial state can be steered to $0$ in exactly $N$ steps if and only if the column space of $A^N$ is contained in that of $R_N(A, B)$.

Null-controllability is weaker than controllability: for $n = m = 1$ and $A = B = 0$, every state is steered to $0$ in one step, while the only state reachable from $0$ is $0$, and $\operatorname{rank} R_N(A, B) = 0 < 1$ for every $N$.

Parts 1 and 4 read off the displayed formula for $x(N)$. Part 2 is the Cayley–Hamilton theorem: every power $A^j$ with $j \ge n$ is a linear combination of $I, A, \dots, A^{n-1}$. For $n = 0$ all conditions hold trivially. The continuous-time counterpart of part 3 is the [Kalman rank condition](is-controllable-on-iff-kalman.md) for $\dot x = A x + B u$.

## Proof depends on

- [Cayley–Hamilton theorem](../../../LinearAlgebra/eigenvalues-and-canonical-forms/characteristic-polynomials-and-the-cayley-hamilt/cayley-hamilton-theorem/aeval-self-charpoly.md): powers $A^j$ with $j \ge n$ add nothing to the column space (part 2).

## Sources

- E. D. Sontag, *Mathematical Control Theory: Deterministic Finite Dimensional Systems*, 2nd ed., Texts in Applied Mathematics 6, Springer, 1998, <http://www.sontaglab.org/FTPDIR/sontag_mathematical_control_theory_springer98.pdf>, Section 3.2: the formula for the state reached from $0$, Theorem 2 and the Cayley–Hamilton argument that follows it (pp. 88–89); Exercise 3.3.14 (p. 99), which characterizes null-controllability without a fixed horizon by the column space of $A^n$ lying in that of $R(A, B)$.
