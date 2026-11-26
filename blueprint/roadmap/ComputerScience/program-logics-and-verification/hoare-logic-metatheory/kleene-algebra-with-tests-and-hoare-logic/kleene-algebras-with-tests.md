# Kleene algebras with tests

A *Kleene algebra* $(K, +, \cdot, {}^\ast, 0, 1)$ is an idempotent semiring under $+$, $\cdot$, $0$ and $1$, ordered by $p \le q \iff p + q = q$, whose star satisfies $1 + pp^\ast \le p^\ast$, $1 + p^\ast p \le p^\ast$, and the induction laws: $q + pr \le r$ implies $p^\ast q \le r$, and $q + rp \le r$ implies $qp^\ast \le r$. A *Kleene algebra with tests* (KAT) is a two-sorted structure $(K, B, +, \cdot, {}^\ast, \bar{\ }, 0, 1)$ with $B \subseteq K$ such that $(K, +, \cdot, {}^\ast, 0, 1)$ is a Kleene algebra and $(B, +, \cdot, \bar{\ }, 0, 1)$ is a Boolean algebra, the complement $\bar{\ }$ being defined only on $B$. The elements of $B$ are *tests*; on tests $\cdot$ is conjunction and $+$ disjunction, and $b \le 1$ for every test. While programs are interpreted by $p ; q = pq$, $\mathbf{if}\ b\ \mathbf{then}\ p\ \mathbf{else}\ q = bp + \bar b q$ and $\mathbf{while}\ b\ \mathbf{do}\ p = (bp)^\ast \bar b$. In a *relational model* $K$ consists of binary relations on a set, with union, relational composition, reflexive transitive closure, the empty relation and the identity, and the tests are subsets of the identity.

## Related topics

- [Kleene algebra with tests](../../kleene-algebra-with-tests/README.md)

## Sources

- D. Kozen, "Kleene algebra with tests", *ACM Transactions on Programming Languages and Systems* 19(3):427–443, 1997, author copy <https://www.cs.cornell.edu/~kozen/Papers/kat.pdf>, Sections 2, 2.1 and 2.2.
- D. Kozen, "On Hoare logic and Kleene algebra with tests", *ACM Transactions on Computational Logic* 1(1), 2000, author copy <https://www.cs.cornell.edu/~kozen/Papers/Hoare.pdf>, Section 2.
