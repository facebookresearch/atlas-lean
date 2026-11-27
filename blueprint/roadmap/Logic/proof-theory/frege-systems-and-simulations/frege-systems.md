# Frege systems

A *Frege system* is a line-based propositional proof system given by finitely many axiom schemes and inference rules over a complete set of connectives, all sound, and implicationally complete: whenever a finite set $\Gamma$ of formulas semantically implies $\varphi$, there is a derivation of $\varphi$ from $\Gamma$. A standard example is the Hilbert-style system with connectives $\to, \bot, \wedge, \vee$, the axiom schemes $A \to (B \to A)$, $(A \to (B \to C)) \to ((A \to B) \to (A \to C))$, $\neg\neg A \to A$, the introduction and elimination schemes for $\wedge$ and $\vee$, and modus ponens as the only rule.

## Depends on

- [Line-based (dag-like) derivations](line-based-derivations.md)
- [Cook–Reckhow propositional proof systems](../../propositional-logic/propositional-proof-complexity/cookreckhow-propositional-proof-systems.md)

## Sources

- S. A. Cook and R. A. Reckhow, "The Relative Efficiency of Propositional Proof Systems", The Journal of Symbolic Logic 44(1), 36–50, 1979: Definitions 2.1–2.2.
- S. Buss and J. Nordström, "Proof Complexity and SAT Solving", in Handbook of Satisfiability, 2nd ed., IOS Press, 2021, Section 7.9.
