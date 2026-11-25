# The square is not operator monotone

There are positive-semidefinite $2 \times 2$ complex matrices $A \le B$ (Loewner order) with $A^2 \not\le B^2$: take

$$
A = \begin{pmatrix} 1 & 1 \\ 1 & 1 \end{pmatrix}, \qquad B = \begin{pmatrix} 2 & 1 \\ 1 & 1 \end{pmatrix},
$$

so that $B - A = \begin{pmatrix} 1 & 0 \\ 0 & 0 \end{pmatrix} \ge 0$ while $B^2 - A^2 = \begin{pmatrix} 3 & 1 \\ 1 & 0 \end{pmatrix}$ has negative determinant; explicitly $x^* (B^2 - A^2) x = -5$ for $x = (1, -4)$. So $t \mapsto t^2$, monotone on $[0, \infty)$, is not operator monotone; compare the Loewner–Heinz theorem (E. A. Carlen, *Trace inequalities and quantum entropy: an introductory course*, lecture-notes draft of May 3, 2009, Theorem 2.6), which asserts operator monotonicity of $t \mapsto t^p$ for $0 \le p \le 1$. The square is operator convex but not operator monotone.

## Background

- [The square is operator convex](sq-convex-comb-le.md): the positive half of the picture for the same function.

## Sources

- E. A. Carlen, *Trace inequalities and quantum entropy: an introductory course*, lecture-notes draft of May 3, 2009, Example 2.2 (non-monotonicity of the square), Definition 2.1 and Theorem 2.6. Theorem numbers refer to that draft.
