# Soundness and implicational completeness of the Hilbert–Frege system

For the Hilbert-style Frege system with modus ponens: if $\varphi$ is derivable from hypotheses $\Gamma$ then every assignment satisfying $\Gamma$ satisfies $\varphi$; conversely, if $\Gamma$ semantically implies $\varphi$ then $\varphi$ is derivable from $\Gamma$. Hence it is a Cook–Reckhow propositional proof system for tautologies.

## Proof sketch

Soundness: each axiom instance is a tautology and modus ponens preserves truth. Completeness: by the deduction theorem and induction on the formula, derive the literal-wise truth-table lemma and eliminate atoms by case analysis using double-negation elimination.

## Depends on

- [Frege systems](frege-systems.md)

## Proof depends on

- [Cook–Reckhow theorem](../../propositional-logic/propositional-proof-complexity/cookreckhow-theorem.md)

## Sources

- S. A. Cook and R. A. Reckhow, "The Relative Efficiency of Propositional Proof Systems", The Journal of Symbolic Logic 44(1), 36–50, 1979.
