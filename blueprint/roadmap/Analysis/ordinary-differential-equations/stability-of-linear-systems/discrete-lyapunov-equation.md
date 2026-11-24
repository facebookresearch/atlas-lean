# Discrete Lyapunov equation for convergent matrices

Let $A \in \mathbb{R}^{n \times n}$. For symmetric matrices write $P > 0$ for positive definite and $Q < 0$ for negative definite. The following are equivalent:

1. $A$ is convergent: every complex eigenvalue of $A$ has modulus less than $1$;
2. for every $Q \in \mathbb{R}^{n \times n}$ the discrete Lyapunov matrix equation

    $$A^\top P A - P = Q$$

    has a unique solution $P \in \mathbb{R}^{n \times n}$, and if $Q < 0$ then $P > 0$;
3. there is a symmetric $P > 0$ with $A^\top P A - P < 0$.

In part 3, $V(x) = x^\top P x$ is a quadratic Lyapunov function for $x^+ = A x$.

For 1 $\Rightarrow$ 2, the geometric bound $\|A^k\| \le M r^k$ with $r < 1$ of [exponential stability of linear difference equations](asymptotic-stability-linear-difference-equations.md) makes $P = -\sum_{k \ge 0} (A^\top)^k Q A^k$ absolutely convergent, and this $P$ solves the equation; a solution of the homogeneous equation $A^\top P A = P$ satisfies $P = (A^\top)^k P A^k \to 0$, which gives uniqueness; and $Q < 0$ makes every term $-(A^\top)^k Q A^k$ positive semidefinite and the $k = 0$ term positive definite.

## Proof depends on

- [Exponential stability of linear difference equations](asymptotic-stability-linear-difference-equations.md): the geometric bound on $\|A^k\|$ for convergent $A$, and the converse used for 3 $\Rightarrow$ 1.

## Sources

- E. D. Sontag, *Mathematical Control Theory: Deterministic Finite Dimensional Systems*, 2nd ed., Texts in Applied Mathematics 6, Springer, 1998, <http://www.sontaglab.org/FTPDIR/sontag_mathematical_control_theory_springer98.pdf>, Section 5.7: Lemma/Exercise 5.7.19, parts 1–3 (p. 231), the discrete-time analogue of Theorem 18 on the same page.
