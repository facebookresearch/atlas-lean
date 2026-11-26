# Intuitionistic propositional logic

Propositions over an atom type with decidable equality are built from atoms by $\wedge$, $\vee$ and $\to$; there is no primitive $\bot$ or $\top$. A theory $T$ is a set of propositions, and $T$ derives a sequent $\Gamma \vdash A$, for a finite set $\Gamma$ of propositions, by natural deduction with the members of $T$ as axioms. A designated bottom atom $\bot$ is fixed, and $\neg A$ is $A \to \bot$. Intuitionistic propositional logic is the theory $\{\bot \to A : A \text{ a proposition}\}$ of all explosion instances.
