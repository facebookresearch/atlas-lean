# The bounded-real lemma

Let $A \in \mathbb{R}^{n \times n}$, $B \in \mathbb{R}^{n \times p}$, $C \in \mathbb{R}^{p \times n}$ and $D \in \mathbb{R}^{p \times p}$, consider $\dot x = Ax + Bu$, $y = Cx + Du$, and its transfer matrix $H(s) = C(sI - A)^{-1}B + D$. Call the system **nonexpansive** if $\int_0^T y^\top y\, dt \le \int_0^T u^\top u\, dt$ for every $T > 0$ and every solution with $x(0) = 0$ and locally square-integrable $u$. Consider the linear matrix inequality in the symmetric variable $P$:

$$P \succ 0, \qquad \begin{bmatrix} A^\top P + PA + C^\top C & PB + C^\top D \\ B^\top P + D^\top C & D^\top D - I \end{bmatrix} \preceq 0 .$$

1. **Sufficiency.** If the inequality has a solution $P$, then $\frac{d}{dt}\big(x^\top Px\big) \le u^\top u - y^\top y$ along every solution, the system is nonexpansive, and $\|H(i\omega)\| \le 1$ for every real $\omega$ with $i\omega$ not an eigenvalue of $A$.
2. **Converse.** If $A$ is Hurwitz and $(A, B, C)$ is minimal, then the inequality is feasible if and only if the system is nonexpansive, if and only if $H(s)^\ast H(s) \preceq I$ for all $\operatorname{Re} s > 0$, that is $\|H\|_\infty \le 1$.

Scaling $C$ and $D$ by $1/\gamma$ turns nonexpansiveness into an $L^2$ gain at most $\gamma$.

**Proof of part 1.** With $\eta = (x, u)$, the derivative $\frac{d}{dt}(x^\top Px) = 2x^\top P(Ax + Bu)$ equals $u^\top u - y^\top y + \eta^\top N\eta$, where $N$ is the block matrix of the inequality, and $N \preceq 0$ gives the dissipation inequality. Integrating from $x(0) = 0$ and using $P \succ 0$ gives nonexpansiveness. For the frequency bound, take $u(t) = e^{i\omega t}u_0$ and $x(t) = e^{i\omega t}(i\omega I - A)^{-1}Bu_0$, a complex solution of the equations; the real and imaginary parts are real solutions, and the dissipation inequality applied to them and added gives $0 = \frac{d}{dt}(x^\ast Px) \le |u_0|^2 - |H(i\omega)u_0|^2$.

## Expansion

The converse needs a construction of $P$ from the frequency-domain bound: by the Kalman–Yakubovich–Popov lemma, or, when $D^\top D \prec I$, from the stabilizing solution of the Riccati equation $A^\top P + PA + C^\top C + (PB + C^\top D)(I - D^\top D)^{-1}(PB + C^\top D)^\top = 0$, which exists exactly when the associated Hamiltonian matrix has no imaginary eigenvalues. The converse rests on one of these two results.

## Background

- [Discrete-time dissipation inequality and an ℓ² gain certificate](discrete-time-dissipation-inequality-and-an-l2-gain-certificate.md): the discrete-time counterpart of part 1

## Sources

- S. Boyd, L. El Ghaoui, E. Feron and V. Balakrishnan, *Linear Matrix Inequalities in System and Control Theory*, SIAM, 1994, <https://web.stanford.edu/~boyd/lmibook/>, Section 2.7.3, the bounded-real lemma: the inequality (2.39) with $A$ stable and $(A, B, C)$ minimal is feasible if and only if the system (2.37) is nonexpansive, equivalently $H(s)^\ast H(s) \le I$ for $\operatorname{Re} s > 0$, and its relation to the Riccati equation (2.40) and the Hamiltonian matrix (pp. 26–27). The proof of part 1 is on the page.
