# Soundness and implicational completeness of the Hilbert–Frege system

For the Hilbert-style Frege system with modus ponens: if $\varphi$ is derivable from hypotheses $\Gamma$ then every assignment satisfying $\Gamma$ satisfies $\varphi$; conversely, if $\Gamma$ semantically implies $\varphi$ then $\varphi$ is derivable from $\Gamma$. Hence it is a Cook–Reckhow propositional proof system for tautologies.

## Proof sketch

Soundness: each axiom instance is a tautology and modus ponens preserves truth. Completeness (Kalmár's method): by the deduction theorem and induction on the formula, derive the literal-wise truth-table lemma and eliminate atoms by case analysis using double-negation elimination; for finite $\Gamma = \{\gamma_1,\dots,\gamma_m\}$ apply this to the tautology $\gamma_1 \to (\dots \to (\gamma_m \to \varphi))$ and use modus ponens.

## Depends on

- [Frege systems](frege-systems.md)
- [Cook–Reckhow propositional proof systems](../../propositional-logic/propositional-proof-complexity/cookreckhow-propositional-proof-systems.md)

## Sources

- S. A. Cook and R. A. Reckhow, "The Relative Efficiency of Propositional Proof Systems", The Journal of Symbolic Logic 44(1), 36–50, 1979.
- E. Mendelson, Introduction to Mathematical Logic, 6th ed., CRC Press, 2015, Section 1.4 (deduction theorem and Kalmár's completeness proof).
