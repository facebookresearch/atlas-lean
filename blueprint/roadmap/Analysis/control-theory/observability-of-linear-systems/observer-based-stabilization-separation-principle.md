# Observer-based stabilization: the separation principle

Let $A \in \mathbb{R}^{n \times n}$, $B \in \mathbb{R}^{n \times m}$ and $C \in \mathbb{R}^{p \times n}$, and let $F \in \mathbb{R}^{m \times n}$ and $L \in \mathbb{R}^{n \times p}$ be fixed gains. Close the loop of the plant $\dot x = A x + B u$, $y = C x$ with the observer-based controller

$$\dot z = (A + LC + BF) z - L y, \qquad u = F z ,$$

whose observer uses the same plant model $(A, B, C)$. In discrete time, replace each derivative by the next value.

1. The closed loop is the linear system on $(x, z)$ with matrix $\begin{bmatrix} A & BF \\ -LC & A + LC + BF \end{bmatrix}$. In the coordinates $(x, e)$ with $e = z - x$, it becomes the block upper triangular matrix

    $$\begin{bmatrix} A + BF & BF \\ 0 & A + LC \end{bmatrix},$$

    by the similarity $T = \begin{bmatrix} I & 0 \\ -I & I \end{bmatrix}$.

2. Hence the characteristic polynomial of the closed loop is $\det(sI - A - BF) \cdot \det(sI - A - LC)$: its eigenvalues are those of $A + BF$ together with those of $A + LC$.

3. If $A + BF$ and $A + LC$ are both Hurwitz (resp. both convergent), the closed loop is Hurwitz (resp. convergent). The origin is then exponentially stable, and every closed-loop solution tends to $0$.

No reachability, observability or pole placement is assumed here: the gains are given. Written with $u = -Kz$ and observer gain $-L$, the triangular form has diagonal blocks $A - BK$ and $A - LC$.

## Proof depends on

- [Observer error convergence and observer pole assignment](observer-error-convergence-and-observer-pole-assignment.md): the error $e = z - x$ obeys the observer error equation
- [Exponential stability of linear differential equations](../../ordinary-differential-equations/stability-of-linear-systems/asymptotic-stability-linear-differential-equations.md): stability of the Hurwitz closed loop
- [Exponential stability of linear difference equations](../../ordinary-differential-equations/stability-of-linear-systems/asymptotic-stability-linear-difference-equations.md): stability of the convergent closed loop

## Sources

- E. D. Sontag, *Mathematical Control Theory: Deterministic Finite Dimensional Systems*, 2nd ed., Texts in Applied Mathematics 6, Springer, 1998, <http://www.sontaglab.org/FTPDIR/sontag_mathematical_control_theory_springer98.pdf>, Section 7.2, proof that Property 3 implies Property 2 in Theorem 32 (pp. 324–325): the interconnection matrix and its similarity to the block triangular form, in continuous and discrete time.
