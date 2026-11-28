# Weakening the context of a derivation

Propositions over an atom type with decidable equality are built from atoms by $\wedge$, $\vee$ and $\to$; there is no primitive $\bot$ or $\top$. A theory $T$ is a set of propositions, and $T$ derives a sequent $\Gamma \vdash A$, for a finite set $\Gamma$ of propositions, by natural deduction with the members of $T$ as axioms. If $\Gamma \subseteq \Delta$, every derivation of $\Gamma \vdash A$ in $T$ is transformed into a derivation of $\Delta \vdash A$ in the same theory $T$.
