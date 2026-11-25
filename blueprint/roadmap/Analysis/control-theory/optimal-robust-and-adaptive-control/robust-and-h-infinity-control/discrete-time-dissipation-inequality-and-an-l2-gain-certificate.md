# Discrete-time dissipation inequality and an ℓ² gain certificate

Let $A \in \mathbb{R}^{n \times n}$, $B \in \mathbb{R}^{n \times m}$, $C \in \mathbb{R}^{p \times n}$ and $D \in \mathbb{R}^{p \times m}$, and consider $x_{k+1} = A x_k + B u_k$, $y_k = C x_k + D u_k$ for $k \ge 0$. Suppose $P \in \mathbb{R}^{n \times n}$ is symmetric positive semidefinite, $\gamma \ge 0$, and

$$M = \begin{bmatrix} A^\top P A - P + C^\top C & A^\top P B + C^\top D \\ B^\top P A + D^\top C & B^\top P B + D^\top D - \gamma^2 I \end{bmatrix} \preceq 0 .$$

1. **Dissipation inequality.** For every initial state $x_0$, every input sequence and every $N \ge 0$,

    $$\sum_{k < N} \|y_k\|^2 \le \gamma^2 \sum_{k < N} \|u_k\|^2 + x_0^\top P x_0 - x_N^\top P x_N .$$

2. **Gain bound.** From $x_0 = 0$, $\sum_{k < N} \|y_k\|^2 \le \gamma^2 \sum_{k < N} \|u_k\|^2$ for every $N$; in particular a square-summable input gives a square-summable output with $\|y\|_2 \le \gamma \|u\|_2$.
3. **Example.** For the scalar system $A = \tfrac12$, $B = C = 1$, $D = 0$, the choice $P = 2$, $\gamma = 2$ gives $M = \begin{bmatrix} -\tfrac12 & 1 \\ 1 & -2 \end{bmatrix}$, which is negative semidefinite (negative diagonal entries and determinant $0$), so the zero-state $\ell^2$ gain is at most $2$. The bound is attained in the limit: the transfer function $1/(z - \tfrac12)$ has modulus $2$ at $z = 1$, the largest value of its modulus on the unit circle.

This is the sufficiency direction only: it does not assert that a certificate exists whenever the gain is at most $\gamma$ (the converse, discrete-time bounded-real lemma), and it gives no internal stability conclusion, since $P$ is only semidefinite.

**Proof.** For each $k$, with $v_k = (x_k, u_k)$, expanding $x_{k+1} = A x_k + B u_k$ and $y_k = C x_k + D u_k$ gives the identity

$$x_{k+1}^\top P x_{k+1} - x_k^\top P x_k + \|y_k\|^2 - \gamma^2 \|u_k\|^2 = v_k^\top M v_k \le 0 .$$

Summing over $k < N$ telescopes the first two terms to $x_N^\top P x_N - x_0^\top P x_0$, which is part 1. Part 2 follows from $x_0 = 0$ and $x_N^\top P x_N \ge 0$, letting $N \to \infty$ for square-summable inputs. In part 3, $A^\top P A - P + C^\top C = \tfrac12 - 2 + 1 = -\tfrac12$, $A^\top P B + C^\top D = 1$ and $B^\top P B + D^\top D - \gamma^2 = 2 - 4 = -2$, so $\det M = 1 - 1 = 0$.

## Sources

- S. Boyd, L. El Ghaoui, E. Feron and V. Balakrishnan, *Linear Matrix Inequalities in System and Control Theory*, SIAM, 1994, <https://web.stanford.edu/~boyd/lmibook/lmibook.pdf>, Section 2.7.3, the bounded-real lemma (pp. 26–27): for the continuous-time system, feasibility of the LMI $\begin{bmatrix} A^\top P + PA + C^\top C & PB + C^\top D \\ B^\top P + D^\top C & D^\top D - I \end{bmatrix} \le 0$, $P > 0$, is equivalent to nonexpansiveness $\int_0^T y^\top y \le \int_0^T u^\top u$ from $x(0) = 0$, under stability and minimality. The discrete-time dissipation identity, the semidefinite certificate and the example are derived on the page.
