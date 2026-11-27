# Peierls–Bogoliubov inequality

Let $E$ be a complex inner product space of finite dimension $n$, let $S$ and $T$ be self-adjoint operators on $E$, let $0 \le t \le 1$ and $C = tS + (1 - t)T$, which is again self-adjoint. For a self-adjoint operator $X$ write $\operatorname{tr} e^X = \sum_j e^{\lambda_j(X)}$, the sum over its eigenvalues with multiplicity. Then

$$
\operatorname{tr} e^{tS + (1 - t)T} \le \big(\operatorname{tr} e^S\big)^t \big(\operatorname{tr} e^T\big)^{1 - t}.
$$

For $n \ge 1$, where all these traces are positive, this says equivalently that $X \mapsto \log \operatorname{tr} e^X$ is convex (E. A. Carlen, *Trace inequalities and quantum entropy: an introductory course*, lecture-notes draft of May 3, 2009, Theorem 2.12). In physics notation, with $Z(H) = \operatorname{tr} e^{-\beta H}$ the partition function and $\beta > 0$, the free energy $-\beta^{-1} \log Z$ is concave in the Hamiltonian (for $n \ge 1$). The proof is Peierls' inequality in the eigenbasis of $C$, followed by Hölder's inequality with exponents $1/t$ and $1/(1 - t)$; the endpoints $t = 0, 1$ are equalities.

## Informally uses

- [Peierls' inequality for the exponential](peierls-exp.md): bounds $\sum_i e^{\langle u_i, S u_i\rangle}$ and $\sum_i e^{\langle u_i, T u_i\rangle}$ by $\operatorname{tr} e^S$ and $\operatorname{tr} e^T$.

## Background

- [Golden–Thompson inequality](../../../../LinearAlgebra/positive-definite-matrices/golden-thompson-inequality/golden-thompson.md): another trace inequality for $\operatorname{tr} e^{A + B}$, from the same circle of statistical-mechanics bounds.

## Sources

- E. A. Carlen, Trace inequalities and quantum entropy: an introductory course, lecture-notes draft of May 3, 2009 (published in Contemp. Math. 529, 2010), Theorem 2.12. Theorem numbers refer to that draft.
