# Reckhow: all Frege systems are polynomially equivalent

Any two Frege systems (over possibly different complete sets of connectives) polynomially simulate each other: there is a polynomial $p$ such that if a tautology has a proof of size $s$ in one system, its translation has a proof of size at most $p(s)$ in the other. Consequently the open problem of superpolynomial Frege lower bounds does not depend on the choice of Frege system.

## Proof sketch

Each axiom scheme and rule of the first system is a tautological implication, hence derivable in the second by implicational completeness; substituting instances costs polynomially. Changing connectives requires translating formulas with a balanced-formula technique to avoid exponential blowup.

## Depends on

- [Frege systems](frege-systems.md)
- [Superpolynomial lower bounds for Frege proofs](../superpolynomial-lower-bounds-for-frege-proofs.md)

## Proof depends on

- [Soundness and implicational completeness of the Hilbert–Frege system](frege-soundness-and-completeness.md)

## Sources

- S. A. Cook and R. A. Reckhow, "The Relative Efficiency of Propositional Proof Systems", The Journal of Symbolic Logic 44(1), 36–50, 1979.
