# Exponential stability of linear differential equations

Let $A$ be a real $n \times n$ matrix and fix any norm on $\mathbb{R}^n$. The following are equivalent:

1. $A$ is [Hurwitz](../../../LinearAlgebra/special-matrices/m-matrices-and-hurwitz-stability/nonsingular-m-matrices/is-hurwitz.md): every complex eigenvalue of $A$ has negative real part;
2. there are $M, c > 0$ with $\|e^{tA} v\| \le M e^{-ct} \|v\|$ for all $t \ge 0$ and $v \in \mathbb{R}^n$;
3. every solution of $\dot \xi = A \xi$ satisfies $\xi(t) \to 0$ as $t \to \infty$.

Condition 2 does not depend on the norm, since all norms on $\mathbb{R}^n$ are equivalent.

1 $\Rightarrow$ 2 is the [exponential decay of a Hurwitz semigroup](../lyapunov-s-indirect-method/exists-norm-exp-smul-mul-vec-le.md), stated there for the maximum norm, and 2 $\Rightarrow$ 3 is immediate since $\xi(t) = e^{tA} \xi(0)$. For 3 $\Rightarrow$ 1 (and directly for 2 $\Rightarrow$ 1), let $\lambda = a + i b$ be an eigenvalue of $A$ with complex eigenvector $v$; then $e^{tA} v = e^{\lambda t} v$, so $|e^{tA} v| = e^{at} |v|$. If $a \ge 0$ this does not tend to $0$, and the real or imaginary part of $e^{tA} v$ is a real solution that does not tend to $0$; under condition 2 the same identity gives $e^{at} \le M' e^{-ct}$ for a constant $M'$, so $a \le -c < 0$.

## Depends on

- [Hurwitz matrix](../../../LinearAlgebra/special-matrices/m-matrices-and-hurwitz-stability/nonsingular-m-matrices/is-hurwitz.md): the definition used in condition 1.

## Proof depends on

- [Exponential decay of a Hurwitz semigroup](../lyapunov-s-indirect-method/exists-norm-exp-smul-mul-vec-le.md): the implication 1 $\Rightarrow$ 2.

## Background

- [Asymptotic stability of linear ODEs with eigenvalues in the open left half-plane](../lyapunov-s-indirect-method/linear-ode-asymptotic-stability.md): the implication 1 $\Rightarrow$ 3 in the maximum norm.
- [Exponential stability of linear difference equations](asymptotic-stability-linear-difference-equations.md): the discrete-time counterpart.

## Sources

- E. D. Sontag, *Mathematical Control Theory: Deterministic Finite Dimensional Systems*, 2nd ed., Texts in Applied Mathematics 6, Springer, 1998, <http://www.sontaglab.org/FTPDIR/sontag_mathematical_control_theory_springer98.pdf>, Appendix C.5: Proposition C.5.1, part 1, with its proof (the eigenvector computation $\|e^{tA} v\| = e^{at} \|v\|$ for an eigenvalue of real part $a$), and Definition C.5.2 (pp. 491–492).
