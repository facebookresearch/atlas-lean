# Reckhow: all Frege systems are polynomially equivalent

Any two Frege systems (over possibly different complete sets of connectives) p-simulate each other: there is a polynomial-time computable function mapping every proof of a tautology $\varphi$ in one system to a proof in the other of the translation of $\varphi$ into the other system's connectives ($\varphi$ itself when the connective sets agree). Consequently the open problem of superpolynomial Frege lower bounds does not depend on the choice of Frege system.

## Proof sketch

Over a common connective set (Cook–Reckhow): each rule of the first system is a sound implication between schemes, hence has a fixed derivation in the second by implicational completeness, and substituting instances multiplies the number of lines by a constant and the formula size by a constant, by a translation computable in polynomial time. Changing connective sets (Reckhow) requires translating every formula into the other basis without exponential blowup, which is the involved part of the proof.

## Depends on

- [Frege systems](frege-systems.md)
- [Superpolynomial lower bounds for Frege proofs](../superpolynomial-lower-bounds-for-frege-proofs.md)

## Sources

- S. A. Cook and R. A. Reckhow, "The Relative Efficiency of Propositional Proof Systems", The Journal of Symbolic Logic 44(1), 36–50, 1979: Theorem 2.3 and Corollary 2.4 (same connective set), and the remark after Corollary 2.4 crediting the case of different connective sets to Reckhow's 1976 Ph.D. thesis (University of Toronto).
- S. Buss and J. Nordström, "Proof Complexity and SAT Solving", in Handbook of Satisfiability, 2nd ed., IOS Press, 2021, Section 7.9.
