# Completeness for truth tables

Let $\Gamma$ be a finite set of propositions and $A$ a
proposition. The sequent $\Gamma \vdash A$ is derivable in classical propositional logic (natural
deduction with every instance of $\neg\neg B \to B$ as an axiom, where $\neg B$ abbreviates
$B \to \bot$) iff every Boolean valuation $v$ of the atoms with $v(\bot) = \mathrm{false}$ that
makes every member of $\Gamma$ true also makes $A$ true.
