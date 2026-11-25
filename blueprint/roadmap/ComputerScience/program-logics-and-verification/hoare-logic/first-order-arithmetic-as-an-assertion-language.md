# First-order arithmetic as an assertion language

The assertion language $\mathcal{N}$ is the first-order predicate calculus with equality over the signature with predicate
symbol $<$, function symbols $+$ and $\cdot$, and constants $0$ and $1$. Its *standard interpretation* has domain $\mathbb{Z}$ and gives
these symbols their usual meanings. Numerical expressions of the while language are terms of $\mathcal{N}$, and Boolean
expressions are quantifier-free formulas of $\mathcal{N}$. A state assigns an integer to each program variable; a state $\sigma$
*satisfies* an assertion $P$ when $P$ is true in the standard interpretation under the variable assignment $\sigma$, with the free
variables of $P$ read as program variables.

For a term or formula $E$, distinct variables $y_1, \dots, y_k$ and terms $t_1, \dots, t_k$, $E^{t_1 \cdots t_k}_{y_1 \cdots y_k}$ denotes the
simultaneous substitution of $t_1, \dots, t_k$ for the free occurrences of $y_1, \dots, y_k$ in $E$, renaming bound variables of $E$
where necessary so that no variable of a $t_i$ becomes bound.

## Depends on

- [Assertion](assertion.md)

## Sources

- S. A. Cook, "Soundness and completeness of an axiom system for program verification", *SIAM Journal on Computing* 7(1):70–90, 1978, <http://www.cs.utoronto.ca/~sacook/homepage/soundness.pdf>: Section 2 (the predicate-calculus language and the example language with symbols $<, =, +, \cdot, 0, 1$), Section 3 (the interpretation of that language in the integers) and the substitution notation.
