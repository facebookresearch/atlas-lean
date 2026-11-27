# Operator monotone and operator convex functions

A real function $f$ is operator convex when $f(tA + (1-t)B) \le t f(A) + (1-t) f(B)$ in the star order for self-adjoint $A, B$ and $0 \le t \le 1$, and operator monotone when $A \le B$ implies $f(A) \le f(B)$ (Carlen, Definition 2.1). The Loewner–Heinz theorem lists the basic examples: on positive semidefinite operators, that is, on spectra in $[0, \infty)$, $t^p$ is operator monotone and operator concave for $0 \le p \le 1$ and operator convex for $1 \le p \le 2$.

- [The square is operator convex, as a convex function](convex-on-mul-self.md)
- [The square is not operator monotone](not-monotone-sq.md)
- [Convex-combination identity for squares](smul-sq-add-smul-sq-sub-sq.md)
- [The square is operator convex](sq-convex-comb-le.md)
- [Operator convexity of $t^p$ for $1 \le p \le 2$ (Loewner–Heinz)](convex-on-cfc-rpow.md)

## Related topics

- [Lieb's concavity theorem](../../../LinearAlgebra/positive-definite-matrices/lieb-s-concavity-theorem/README.md): its one-variable cases follow from the operator concavity of $t^q$.
- [Peierls and Klein inequalities](../../operator-theory/eigenvalue-inequalities/peierls-and-klein-inequalities/README.md): convexity of trace functions, the scalar notion that operator convexity strengthens.
