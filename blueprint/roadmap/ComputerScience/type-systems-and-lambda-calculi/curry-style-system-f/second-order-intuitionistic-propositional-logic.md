# Second-order intuitionistic propositional logic

Formulas of *second-order propositional logic* are built from propositional variables, $\bot$, $\to$, $\wedge$, $\vee$ and the quantifiers $\forall p$ and $\exists p$ over propositional
variables. Its intuitionistic natural deduction system has the rules of intuitionistic propositional logic together with

- ($\forall$I) from $\Gamma \vdash \varphi$ infer $\Gamma \vdash \forall p\, \varphi$, if $p$ is not free in $\Gamma$; ($\forall$E) from $\Gamma \vdash \forall p\, \varphi$ infer $\Gamma \vdash \varphi[p := \vartheta]$ for any formula $\vartheta$;
- ($\exists$I) from $\Gamma \vdash \varphi[p := \vartheta]$ infer $\Gamma \vdash \exists p\, \varphi$; ($\exists$E) from $\Gamma \vdash \exists p\, \varphi$ and $\Gamma, \varphi \vdash \psi$ infer $\Gamma \vdash \psi$, if $p$ is not free in
  $\Gamma$ or $\psi$.

Quantifiers range over all propositions, including the formula being defined, so the logic is impredicative.

## Sources

- M. H. B. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, University of Copenhagen, May 1998: Section 12.1, the definition of second-order formulas and Definition 12.1.2 (natural deduction), with the remark on impredicativity before it.
