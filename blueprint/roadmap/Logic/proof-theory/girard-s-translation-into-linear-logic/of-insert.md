# Separating a new hypothesis in the translation

Let $f$ map propositional atoms to CLL
propositions, let $\Gamma$ be a finite set of propositional formulas, $A$ a propositional formula
and $c$ a CLL proposition. Write $B^\circ$ for Girard's translation of a formula $B$ with atoms
translated by $f$, and $?\Delta^{\circ\perp}$ for the multiset of the propositions
$?\big((B^\circ)^\perp\big)$ for $B \in \Delta$. If the CLL sequent
$\vdash c, ?(\Gamma \cup \{A\})^{\circ\perp}$ is provable, then so is
$\vdash ?\big((A^\circ)^\perp\big), c, ?\Gamma^{\circ\perp}$.

When $A \in \Gamma$ the conclusion follows by weakening.
