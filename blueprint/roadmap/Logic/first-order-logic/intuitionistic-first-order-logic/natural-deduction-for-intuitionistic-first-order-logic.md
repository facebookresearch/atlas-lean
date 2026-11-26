# Natural deduction for intuitionistic first-order logic

Over a first-order signature, formulas are built from atomic formulas and $\bot$ with $\wedge$, $\vee$, $\to$, $\forall$ and $\exists$, identified up to renaming of bound variables. Derivability $\Gamma \vdash \varphi$ in intuitionistic first-order logic (IQC) extends [natural deduction for IPC](../../propositional-logic/intuitionistic-propositional-logic/natural-deduction-for-intuitionistic-propositional-logic.md) by the rules

- ($\forall$I) from $\Gamma \vdash \varphi$ infer $\Gamma \vdash \forall x\, \varphi$, if $x$ is not free in $\Gamma$; ($\forall$E) from $\Gamma \vdash \forall x\, \varphi$ infer $\Gamma \vdash \varphi[x := t]$;
- ($\exists$I) from $\Gamma \vdash \varphi[x := t]$ infer $\Gamma \vdash \exists x\, \varphi$; ($\exists$E) from $\Gamma \vdash \exists x\, \varphi$ and $\Gamma, \varphi \vdash \psi$ infer $\Gamma \vdash \psi$, if $x$ is not free in $\Gamma$ or $\psi$.

## Depends on

- [Natural deduction for intuitionistic propositional logic](../../propositional-logic/intuitionistic-propositional-logic/natural-deduction-for-intuitionistic-propositional-logic.md)

## Sources

- M. H. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, 1998 (published as volume 149 of *Studies in Logic and the Foundations of Mathematics*, Elsevier, 2006), Section 9.1 (syntax of first-order logic) and Section 9.3 (the natural deduction rules for quantifiers and the convention on renaming of bound variables).
