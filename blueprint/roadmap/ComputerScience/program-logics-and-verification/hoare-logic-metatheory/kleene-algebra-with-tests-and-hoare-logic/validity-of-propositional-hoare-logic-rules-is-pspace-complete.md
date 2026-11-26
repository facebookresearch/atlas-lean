# Validity of propositional Hoare logic rules is PSPACE-complete

Deciding whether a rule of propositional Hoare logic, from premises $\{b_1\}\, p_1\, \{c_1\}, \dots, \{b_n\}\, p_n\, \{c_n\}$ to a conclusion $\{b\}\, p\, \{c\}$, is valid over all relational interpretations is PSPACE-complete. Membership in PSPACE follows by reducing the rule to a single KAT equation, through [completeness for Horn formulas with zero premises](kat-is-complete-for-relationally-valid-horn-formulas.md), and deciding it with the [PSPACE procedure for KAT](equational-theory-of-kat-is-pspace-complete.md). PSPACE-hardness holds even when the premises refer only to a single atomic program; it does not follow directly from the hardness of the equational theory, since valid equations of the restricted form $q = 0$ are only NP-complete.

## Depends on

- [Kleene algebras with tests](kleene-algebras-with-tests.md)
- [Polynomial space for decision problems](../../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/pspace.md)

## Proof depends on

- [KAT is complete for relationally valid Horn formulas with zero premises](kat-is-complete-for-relationally-valid-horn-formulas.md)
- [The equational theory of KAT is PSPACE-complete](equational-theory-of-kat-is-pspace-complete.md)

## Sources

- D. Kozen, "On Hoare logic and Kleene algebra with tests", *ACM Transactions on Computational Logic* 1(1), 2000, author copy <https://www.cs.cornell.edu/~kozen/Papers/Hoare.pdf>, Section 2.1 (the decision problem) and Section 5, Theorem 5.1.
