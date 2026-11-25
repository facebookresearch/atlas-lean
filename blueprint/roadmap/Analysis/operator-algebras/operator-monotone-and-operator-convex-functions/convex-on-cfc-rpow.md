# Operator convexity of $t^p$ for $1 \le p \le 2$ (Loewner–Heinz)

For $1 \le p \le 2$ the map $A \mapsto A^p$, defined by the continuous functional calculus, is convex on positive-semidefinite complex matrices for the Loewner order: $(t A + (1 - t) B)^p \le t A^p + (1 - t) B^p$ for $0 \le t \le 1$ (E. A. Carlen, *Trace inequalities and quantum entropy: an introductory course*, lecture-notes draft of May 3, 2009, Theorem 2.6).

Complex matrices form a C⋆-algebra for the operator norm, whose star order is the Loewner order, so this is the matrix case of the operator convexity of $t^p$, $1 \le p \le 2$, on the positive elements of a C⋆-algebra; matrices of size $0$ are a trivial case. The monotone and concave half, $0 \le p \le 1$, holds as well.

## Background

- [The square is operator convex](sq-convex-comb-le.md): the endpoint $p = 2$, proved directly, for all self-adjoint elements of any star-ordered real algebra.
- [The square is not operator monotone](not-monotone-sq.md): why the monotone half stops at $p = 1$.

## Sources

- E. A. Carlen, Trace inequalities and quantum entropy: an introductory course, lecture-notes draft of May 3, 2009 (published in Contemp. Math. 529, 2010), Definition 2.1 and Theorem 2.6. Theorem numbers refer to that draft.
- Physlib, Loewner–Heinz convexity of $t^p$ for $1 \le p \le 2$ in C⋆-algebras (file `QuantumInfo/ForMathlib/HayataGroup/TraceInequality/LownerHeinzCore.lean`).
