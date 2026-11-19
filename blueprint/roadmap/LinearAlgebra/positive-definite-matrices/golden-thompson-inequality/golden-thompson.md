# Golden–Thompson inequality

For Hermitian complex matrices $A$ and $B$, $\operatorname{tr} e^{A+B} \le \operatorname{tr}(e^A e^B)$ (P. J. Forrester and C. J. Thompson, *The Golden–Thompson
inequality — historical aspects and random matrix applications*, arXiv:1408.2008v1, equation
(1.1); S. Golden, Phys. Rev. 137 (1965) B1127; C. J. Thompson, J. Math. Phys. 6 (1965) 1812).
Both sides are real numbers: the left side because $e^{A+B}$ is positive definite, the right side by [the result on the right side](trace-exp-mul-exp-nonneg.md).

Golden proved it for nonnegative definite $A, B$ and Thompson for all Hermitian $A, B$, both in 1965 (Forrester and Thompson, introduction). For commuting $A$ and $B$ it is an equality; for noncommuting ones it can be strict.

The usual proof combines the Lie–Trotter product formula $e^{A+B} = \lim_m (e^{A/m} e^{B/m})^m$ with the inequality $|\operatorname{tr}(XY)^{2^k}| \le \operatorname{tr}(X^2 Y^2)^{2^{k-1}}$ for positive $X, Y$.

## Background

- [Golden–Thompson equality for commuting matrices](trace-exp-add-of-commute.md): the equality case.
- [The right side of Golden–Thompson is a nonnegative real](trace-exp-mul-exp-nonneg.md): why the inequality compares two real numbers.
- [Peierls–Bogoliubov inequality for Hermitian matrices](../../../Analysis/operator-theory/eigenvalue-inequalities/peierls-and-klein-inequalities/re-trace-exp-convex-comb-le.md): a companion trace-exponential bound, the convexity of $A \mapsto \log \operatorname{tr} e^A$.
- [Exponential limits and the Lie–Trotter formula](../../../Analysis/operator-algebras/exponential-limits-and-the-lie-trotter-formula/README.md): the product formula $e^{a+b} = \lim (e^{a/n} e^{b/n})^n$, valid in complete normed algebras, which the usual proof uses.

## Sources

- P. J. Forrester and C. J. Thompson, The Golden–Thompson inequality — historical aspects and random matrix applications, arXiv:1408.2008v1 (2014), equation (1.1).
- S. Golden, Lower bounds for the Helmholtz function, Phys. Rev. 137 (1965) B1127–B1128.
- C. J. Thompson, Inequality with applications in statistical mechanics, J. Math. Phys. 6 (1965) 1812–1813.
