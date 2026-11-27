# Heyting arithmetic

*Heyting arithmetic* HA is the first-order theory in the language of arithmetic, extended by a function symbol for every primitive recursive function,
whose axioms and rules are those of intuitionistic first-order logic, the axioms of [Peano arithmetic](../../first-order-logic/peano-arithmetic-and-robinson-s-q/patheory.md) (including induction for every
formula), and the defining equations of the primitive recursive functions. Here intuitionistic first-order logic with equality is natural deduction for
sequents $\Gamma \vdash \varphi$ with the assumption rule, ex falso ($\Gamma \vdash \bot$ gives $\Gamma \vdash \varphi$), introduction and elimination rules for $\to$, $\wedge$ and $\vee$,
($\forall$I) from $\Gamma \vdash \varphi$ infer $\Gamma \vdash \forall x\, \varphi$ if $x$ is not free in $\Gamma$, ($\forall$E) from $\Gamma \vdash \forall x\, \varphi$ infer $\Gamma \vdash \varphi[t/x]$,
($\exists$I) from $\Gamma \vdash \varphi[t/x]$ infer $\Gamma \vdash \exists x\, \varphi$, ($\exists$E) from $\Gamma \vdash \exists x\, \varphi$ and $\Gamma, \varphi \vdash \psi$ infer $\Gamma \vdash \psi$ if $x$ is not
free in $\Gamma$ or $\psi$, and the equality axioms $t = t$ and $s = t \wedge \varphi[s/x] \to \varphi[t/x]$; there is no reductio ad absurdum, so $\varphi \vee \neg\varphi$ and $\neg\neg\varphi \to \varphi$
are not axioms. Adding these function symbols with their defining equations is a conservative
extension, so it is a technical convenience.

## Depends on

- [Peano arithmetic](../../first-order-logic/peano-arithmetic-and-robinson-s-q/patheory.md)

## Sources

- M. H. B. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, University of Copenhagen, May 1998: Section 11.4, the definition of HA.
