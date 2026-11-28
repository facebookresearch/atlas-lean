# Derivation of the canonical tautology

Propositions over an atom type with decidable equality are built from atoms by $\wedge$, $\vee$ and $\to$; there is no primitive $\bot$ or $\top$. A theory $T$ is a set of propositions, and $T$ derives a sequent $\Gamma \vdash A$, for a finite set $\Gamma$ of propositions, by natural deduction with the members of $T$ as axioms. For an atom type with a chosen atom $p$, the fixed tautology $\top$ is $p \to p$. In every theory $T$ there is a derivation of $\top$ from the empty context: assume $p$ and discharge it by implication introduction.
