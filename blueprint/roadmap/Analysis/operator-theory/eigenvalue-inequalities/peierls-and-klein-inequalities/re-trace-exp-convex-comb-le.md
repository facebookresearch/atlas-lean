# Peierls–Bogoliubov inequality for Hermitian matrices

Let $A$ and $B$ be Hermitian complex square matrices and $0 \le t \le 1$. With the matrix exponential,

$$
\operatorname{Re} \operatorname{tr} e^{tA + (1 - t)B} \le \big(\operatorname{Re} \operatorname{tr} e^A\big)^t \big(\operatorname{Re} \operatorname{tr} e^B\big)^{1 - t};
$$

for matrices of positive size this says equivalently that $A \mapsto \log \operatorname{tr} e^A$ is convex on Hermitian matrices (E. A. Carlen, *Trace inequalities and quantum entropy: an introductory course*, lecture-notes draft of May 3, 2009, Theorem 2.12). Both traces on the right are positive reals, being sums of exponentials of eigenvalues. The bound is an equality when $A = B$; for commuting $A$ and $B$ it is Hölder's inequality for the joint eigenvalues.

## Informally uses

- [Peierls–Bogoliubov inequality](sum-exp-eigenvalues-convex-comb-le.md): the operator form, applied to the operators of $A$ and $B$ on $\mathbb{C}^n$; the matrix trace exponential is the exponential sum of the eigenvalues.

## Background

- [Golden–Thompson inequality](../../../../LinearAlgebra/positive-definite-matrices/golden-thompson-inequality/golden-thompson.md): the other classical upper bound on $\operatorname{tr} e^{A + B}$-type quantities.

## Sources

- E. A. Carlen, Trace inequalities and quantum entropy: an introductory course, lecture-notes draft of May 3, 2009 (published in Contemp. Math. 529, 2010), Theorem 2.12. Theorem numbers refer to that draft.
