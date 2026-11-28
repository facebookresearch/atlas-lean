# Logic of bunched implications

This node covers the logic of bunched implications (BI), introduced by O'Hearn and Pym (1999): the
combination of intuitionistic propositional logic with multiplicative intuitionistic linear logic,
with an additive conjunction and implication and a multiplicative conjunction and implication side by
side, so that contexts ("bunches") are built with two different combining operations. BI is closely
connected with the propositional fragment of separation logic. Its literature contains several
algebraic and relational semantics (BI-algebras, ternary relational and resource semantics), some of
which capture only fragments of the logic or use more complex clauses for some connectives, such as
Beth's clause for disjunction.

## Expansion

Formulas and bunches, natural deduction NBI with cut admissibility, the sequent calculus LBI with cut
elimination, conservativity over intuitionistic propositional logic, BI-algebras with soundness and
completeness, and the elementary, Grothendieck and inconsistent-world resource semantics with their
soundness, completeness and incompleteness results are expanded in
[Foundations of bunched implications](bunched-implications-foundations/README.md). Still to expand:
decidability or undecidability of provability; the equivalence of NBI and LBI; conservativity over
multiplicative intuitionistic linear logic; soundness and completeness for bicartesian doubly closed
categories; the ternary relational semantics and resource tableaux; and Boolean BI, Classical BI and the
non-commutative variant, which are separate logics.

## Status

A 2026 preprint by Galatos, Jipsen, Knudstorp and Ramanayake states that provability in BI is
undecidable, by encoding Wang tilings into its ternary relational semantics, contrary to a
long-standing expectation that BI might be decidable, and identifies gaps in earlier publications
claiming decidability; the statement here follows the preprint's abstract.

## Sources

- A. V. Gheorghiu and D. J. Pym, "Semantical analysis of the logic of bunched implications", preprint
  (2022), abstract and introduction. <https://arxiv.org/abs/2210.05348>
- P. Jipsen and T. Litak, "An algebraic glimpse at bunched implications and separation logic",
  preprint (2017), abstract. <https://arxiv.org/abs/1709.07063>
- N. Galatos, P. Jipsen, S. B. Knudstorp and R. Ramanayake, "The logic of bunched implications is
  undecidable", preprint (2026), abstract. <https://arxiv.org/abs/2603.01595>
