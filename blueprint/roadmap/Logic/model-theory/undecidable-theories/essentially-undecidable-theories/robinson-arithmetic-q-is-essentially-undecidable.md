# Robinson arithmetic Q is essentially undecidable

Robinson's finitely axiomatized arithmetic Q is essentially undecidable: every consistent extension of Q in its language is undecidable. Moreover Q is minimal with this property for its standard axiomatization.

**Theorem (Tarski, Mostowski and Robinson).** A first-order theory $U$ is *essentially undecidable* if every consistent extension of $U$ in the same language is undecidable. [Robinson's arithmetic Q](../../../first-order-logic/peano-arithmetic-and-robinson-s-q/qtheory.md), axiomatized by its seven standard axioms, is essentially undecidable. Moreover, every theory axiomatized by a proper subset of these seven axioms has a decidable consistent extension.

In particular Q itself, and every consistent theory in the language of arithmetic that contains Q, such as Peano arithmetic, is undecidable.

## Depends on

- [Robinson's arithmetic Q](../../../first-order-logic/peano-arithmetic-and-robinson-s-q/qtheory.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The classical proof shows that every recursive function is representable in Q, and then applies a diagonal argument: a consistent decidable extension of Q would make the set of Gödel numbers of its theorems representable in it, which yields a sentence that is provable iff it is not. A good expansion links pages for the representability of recursive functions in Q and for the diagonal argument, which have none yet; the minimality clause needs, for each axiom, a decidable consistent extension of the remaining six (Chapter 2, Theorem 11 of the original).

## Sources

- A. Tarski, A. Mostowski and R. M. Robinson, *Undecidable Theories*, Studies in Logic and the Foundations of Mathematics, North-Holland, 1953 (original source, cited beside the copy read): Chapter 2.
- J. Murwanashyaka, F. Pakhomov and A. Visser, "There are no minimal essentially undecidable theories", *Journal of Logic and Computation* 34(6):1159–1171, 2024, doi:10.1093/logcom/exad005; read as arXiv:2207.08174v2, <https://arxiv.org/abs/2207.08174v2>: Section 1 (minimality of Q, citing Chapter 2, Theorem 11 of the book) and Section 2 (Q and R as essentially undecidable theories).
