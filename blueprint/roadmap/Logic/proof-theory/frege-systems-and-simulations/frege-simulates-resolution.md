# Frege polynomially simulates resolution

Frege systems polynomially simulate resolution: every resolution refutation of a CNF formula translates into a Frege refutation (a derivation of $\bot$ from formula translations of its clauses) of size polynomial in the size of the resolution refutation. Thus Frege systems are at least as strong as resolution, and superpolynomial Frege lower bounds would imply them for resolution but not conversely.

## Proof sketch

Translate a clause $\ell_1 \vee \dots \vee \ell_k$ as the formula $\overline{\ell_1} \to (\overline{\ell_2} \to \dots \to (\overline{\ell_k} \to \bot))$, where $\overline{v} = v \to \bot$ and $\overline{v \to \bot} = v$. A single resolution step from translations of $A \vee v$ and $B \vee \neg v$ to the translation of $A \vee B$ is derived by a fixed polynomial-size schema (permuting antecedents and cutting on $v$), uniform in the clause widths. (Derived, not stated by the sources: with this encoding a resolution refutation with $s$ lines over $N$ variables becomes a Frege refutation with $s \cdot \mathrm{poly}(N)$ lines.)

## Depends on

- [Frege systems](frege-systems.md)
- [Resolution refutation](../../propositional-logic/resolution-size-and-width/is-resolution-refutation.md)

## Proof depends on

- [Soundness and implicational completeness of the Hilbert–Frege system](frege-soundness-and-completeness.md)

## Sources

- S. A. Cook and R. A. Reckhow, "The Relative Efficiency of Propositional Proof Systems", The Journal of Symbolic Logic 44(1), 36–50, 1979.
- S. Buss and J. Nordström, "Proof Complexity and SAT Solving", in Handbook of Satisfiability, 2nd ed., IOS Press, 2021, Section 7.9 (Frege systems are strictly stronger than resolution; even bounded-depth Frege systems polynomially simulate resolution).
