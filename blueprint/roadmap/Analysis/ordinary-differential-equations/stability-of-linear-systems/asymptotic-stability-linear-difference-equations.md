# Exponential stability of linear difference equations

Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, let $A \in \mathbb{K}^{n \times n}$ and fix any norm on $\mathbb{K}^{n \times n}$. The following are equivalent:

1. every complex eigenvalue of $A$ has modulus less than $1$ ($A$ is **convergent**, or discrete-time Hurwitz, also called a Schur matrix);
2. there are $M > 0$ and $0 \le r < 1$ with $\|A^k\| \le M r^k$ for every $k \ge 0$;
3. $A^k x \to 0$ as $k \to \infty$ for every $x \in \mathbb{K}^n$; equivalently, every solution of $\xi(t + 1) = A \xi(t)$ tends to $0$.

Condition 2 does not depend on the norm, since all norms on $\mathbb{K}^{n \times n}$ are equivalent. Moreover, in condition 2 any $r$ strictly between the largest eigenvalue modulus and $1$ can be used.

Sontag's proof of 1 $\Leftrightarrow$ 3: by the Jordan form, for $k \ge n$ each entry of $A^k$ is a finite linear combination of terms $c\, k^i \lambda^k$ with $\lambda$ a nonzero eigenvalue of $A$ and $i < n$ (Jordan blocks for the eigenvalue $0$ are nilpotent and contribute nothing once $k \ge n$); these tend to $0$ under condition 1, and indeed are $O(r^k)$ for every $r$ larger than all $|\lambda|$, which gives 1 $\Rightarrow$ 2. Conversely, if $|\lambda| \ge 1$ for an eigenvalue $\lambda$ with eigenvector $v$, then $A^k v = \lambda^k v$ does not tend to $0$, and for real $A$ its real or imaginary part is a real solution that does not. Finally 2 $\Rightarrow$ 3 is immediate.

## Proof depends on

- [Jordan normal form](../../../LinearAlgebra/eigenvalues-and-canonical-forms/jordan-normal-form/exists-jordan-normal-form-of-splits.md): the entries of $A^k$ as combinations of $k^i \lambda^k$.

## Background

- [Exponential stability of linear differential equations](asymptotic-stability-linear-differential-equations.md): the continuous-time counterpart.

## Sources

- E. D. Sontag, *Mathematical Control Theory: Deterministic Finite Dimensional Systems*, 2nd ed., Texts in Applied Mathematics 6, Springer, 1998, <http://www.sontaglab.org/FTPDIR/sontag_mathematical_control_theory_springer98.pdf>, Appendix C.5: Proposition C.5.1, part 2, with its proof, and Definition C.5.2 (pp. 491–492); the description of the entries of $A^k$ refers to Lemma A.3.2 in Appendix A.3.
