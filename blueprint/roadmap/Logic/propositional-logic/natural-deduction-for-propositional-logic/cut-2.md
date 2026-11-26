# Cut rule for derivability

Propositions over an atom type with decidable equality are built from atoms by $\wedge$, $\vee$ and $\to$; there is no primitive $\bot$ or $\top$. A theory $T$ is a set of propositions, and $T$ derives a sequent $\Gamma \vdash A$, for a finite set $\Gamma$ of propositions, by natural deduction with the members of $T$ as axioms. If $T$ derives $\Gamma \vdash A$ and $\Delta \cup \{A\} \vdash B$, then $T$ derives $\Gamma \cup \Delta \vdash B$. This states preservation of derivability; the transformation of derivations is the separate cut rule for derivations.
