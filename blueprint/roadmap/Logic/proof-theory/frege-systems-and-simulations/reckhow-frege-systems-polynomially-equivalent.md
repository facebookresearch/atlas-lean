# Reckhow: all Frege systems are polynomially equivalent

Any two Frege systems (over possibly different complete sets of connectives) polynomially simulate each other: there is a polynomial $p$ such that if a tautology has a proof of size $s$ in one system, its translation has a proof of size at most $p(s)$ in the other. Consequently the open problem of superpolynomial Frege lower bounds does not depend on the choice of Frege system.

## Proof sketch

Over a common connective set (Cook–Reckhow): each rule of the first system is a sound implication between schemes, hence has a fixed derivation in the second by implicational completeness, and substituting instances multiplies the number of lines by a constant and the formula size by a constant. Changing connective sets (Reckhow) requires translating every formula into the other basis without exponential blowup, which is the involved part of the proof.

## Depends on

- [Frege systems](frege-systems.md)
- [Superpolynomial lower bounds for Frege proofs](../superpolynomial-lower-bounds-for-frege-proofs.md)

## Sources

- S. A. Cook and R. A. Reckhow, "The Relative Efficiency of Propositional Proof Systems", The Journal of Symbolic Logic 44(1), 36–50, 1979: Theorem 2.3 and Corollary 2.4 (same connective set), and the remark after Corollary 2.4 crediting the case of different connective sets to Reckhow's 1976 Ph.D. thesis (University of Toronto).
- S. Buss and J. Nordström, "Proof Complexity and SAT Solving", in Handbook of Satisfiability, 2nd ed., IOS Press, 2021, Section 7.9.
