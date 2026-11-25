# Determinant of the matrix exponential

For every complex square matrix $A$ indexed by a
finite set, $\det(e^A) = e^{\operatorname{tr} A}$, where $e^A$ is the matrix exponential. This
identity is sometimes called Jacobi's formula.

Proof: the three cases of B. C. Hall, An Elementary Introduction to Groups and Representations,
https://arxiv.org/abs/math-ph/0005032, Theorem 3.10. The Jordan-Chevalley decomposition writes
$A = N + S$ with $N$ nilpotent, $S$ semisimple and $NS = SN$, so $e^A = e^N e^S$. Diagonalizing
$S$ gives $\det(e^S) = e^{\operatorname{tr} S}$. For the nilpotent part, where Hall uses a
strictly upper-triangular form, $e^N - I$ is nilpotent, so $\det(e^N) = 1$, while
$\operatorname{tr} N = 0$.

## Sources

- B. C. Hall, Lie Groups, Lie Algebras, and Representations, 2nd ed., Springer (2015), Proposition 2.23.
