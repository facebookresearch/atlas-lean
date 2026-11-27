# Termination of linear loops with polynomial guards over the integers is undecidable

For single while loops whose body applies a fixed rational linear map and whose guard is a conjunction of polynomial inequalities, it is undecidable whether the loop terminates on every integer input. This holds for strict and for non-strict inequalities.

**Setting (Xia and Zhang).** Consider loops

$$
\mathtt{P_1}:\quad \mathbf{while}\ (P(X) > 0)\ \{X := AX\},
$$

where $X = (x_1, \dots, x_N)^{\mathsf{T}}$ is the vector of program variables, $P(X) = (P_1(X), \dots, P_m(X))^{\mathsf{T}}$ is a vector of polynomials in $\mathbb{Q}[X]$ and $P(X) > 0$ means $P_i(X) > 0$ for every $i$, and $A$ is an $N \times N$ matrix over $\mathbb{Q}$. $\mathtt{P'_1}$ is the same loop with guard $P(X) \ge 0$. A loop is *terminating over* $\mathbb{Z}$ if it terminates for every input $X \in \mathbb{Z}^N$, the iterates $A^k X$ being rational vectors.

**Theorem (Xia and Zhang).** Termination of loops of the form $\mathtt{P_1}$ over $\mathbb{Z}$ is undecidable, and so is termination of loops of the form $\mathtt{P'_1}$ over $\mathbb{Z}$.

The same paper gives, under an additional assumption, an algorithm deciding termination of $\mathtt{P_1}$ over $\mathbb{R}$, and conjectures that termination over $\mathbb{R}$ is undecidable in general.

## Depends on

None.

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

For a polynomial $f(x_1, \dots, x_m)$ with integer coefficients, take the loop $\mathbf{while}\ (x_{m+1} - f(x_1, \dots, x_m)^2 > 0)\ \{X := AX\}$ with $A = \mathrm{diag}(1, \dots, 1, 1/2)$. The first $m$ variables never change and $x_{m+1}$ is halved at each step. If $f$ has an integer root $(y_1, \dots, y_m)$, the input $(y_1, \dots, y_m, 1)$ keeps the guard $2^{-k} > 0$ true forever. If $f$ has no integer root, $f(x_1, \dots, x_m)^2 \ge 1$ on every integer input, and $2^{-k} x_{m+1}$ eventually drops below it. So the loop terminates over $\mathbb{Z}$ exactly when $f$ has no integer root, which is undecidable by Hilbert's tenth problem; the same argument works with $\ge$.

## Sources

- Bican Xia and Zhihai Zhang, "Termination of linear programs with nonlinear constraints", Journal of Symbolic Computation 45(11), pp. 1234–1249, 2010, <https://doi.org/10.1016/j.jsc.2010.06.006>; the loop $\mathtt{P_1}$ of Section 1 and Lemma 1, Theorem 1 and Theorem 2 (main statement) of Section 2 ("Undecidability of $\mathtt{P_1}$ over $\mathbb{Z}$") of arXiv:0904.3588v1, read at <https://arxiv.org/abs/0904.3588v1>.
