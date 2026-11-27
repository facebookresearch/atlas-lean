# KAT is complete for relationally valid Horn formulas with premises of the form $r = 0$

Every universal Horn formula $r_1 = 0 \wedge \dots \wedge r_n = 0 \Rightarrow p = q$ between terms of [Kleene algebra with tests](kleene-algebras-with-tests.md) that is true in all relational models is a theorem of KAT. In particular every relationally valid rule of propositional Hoare logic is derivable in KAT, which strengthens the [subsumption of Hoare logic](kat-subsumes-propositional-hoare-logic.md); such rules need not be derivable in propositional Hoare logic itself. The proof reduces the premises to a single equation $r = 0$, with $r = r_1 + \dots + r_n$, and shows that the formula is equivalent to the equation $p + uru = q + uru$, where $u$ is the sum of all primitive actions, starred; that equation is then provable by completeness of KAT for valid equations.

## Depends on

- [Kleene algebras with tests](kleene-algebras-with-tests.md)

## Proof depends on

- [Guarded strings are complete for Kleene algebra with tests](guarded-strings-are-complete-for-kat.md)

## Related topics

- [Kleene algebra with tests subsumes propositional Hoare logic](kat-subsumes-propositional-hoare-logic.md)

## Sources

- D. Kozen, "On Hoare logic and Kleene algebra with tests", *ACM Transactions on Computational Logic* 1(1), 2000, author copy <https://www.cs.cornell.edu/~kozen/Papers/Hoare.pdf>, Section 4, Theorem 4.1 and Corollary 4.2.
