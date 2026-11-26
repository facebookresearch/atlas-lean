# Gödel's Dialectica interpretation of Heyting arithmetic

Work in System T with booleans and product types, and for a term $D$ of type $\mathrm{bool}$ whose free variable is $z : \sigma$ write $T \models D$ if
$D[z := Z] =_T \mathrm{t}$ for every closed $Z : \sigma$. To each formula $\varphi$ of arithmetic assign by induction a formula
$\varphi^D = \exists x^\sigma\, \forall y^\tau\, \varphi_D(x, y)$ with $\varphi_D$ a term of type $\mathrm{bool}$:

- for an atomic (primitive recursive) $\varphi$, $\varphi_D$ is a term defining the relation, with dummy $x, y$;
- if $\varphi^D = \exists x \forall y\, \varphi_D(x, y)$ and $\psi^D = \exists u \forall v\, \psi_D(u, v)$, then
  $(\varphi \wedge \psi)^D = \exists x u\, \forall y v\, (\varphi_D(x, y) \wedge \psi_D(u, v))$,
  $(\varphi \vee \psi)^D = \exists z^{\mathrm{nat}} x u\, \forall y v\, ((z = 0 \to \varphi_D(x, y)) \wedge (z \ne 0 \to \psi_D(u, v)))$,
  $(\varphi \to \psi)^D = \exists u_1 y_1\, \forall x v\, (\varphi_D(x, y_1 x v) \to \psi_D(u_1 x, v))$ and
  $(\neg \varphi)^D = \exists z\, \forall x\, \neg \varphi_D(x, z x)$;
- if $\varphi^D = \exists x \forall y\, \varphi_D(x, y, z)$ with $z : \mathrm{nat}$ free, then $(\exists z\, \varphi)^D = \exists z x\, \forall y\, \varphi_D(x, y, z)$ and
  $(\forall z\, \varphi)^D = \exists x_1\, \forall y z\, \varphi_D(x_1 z, y, z)$.

Say $T \models \exists x \forall y\, D$ if there is a term $X$, in which $y$ is not free, with $T \models D[x := X]$.

**Theorem (Gödel).** If Heyting arithmetic proves $\varphi$, then $T \models \varphi^D$. In particular HA is consistent, since $T \models \bot^D$ would give $\mathrm{f} =_T \mathrm{t}$.

## Depends on

- [Gödel's System T](godel-s-system-t.md)

## Proof depends on

- [Church–Rosser property of System T](church-rosser-property-of-system-t.md)

## Expansion

This page becomes ready once:

- Heyting arithmetic: intuitionistic first-order arithmetic with the Peano axioms and induction (statement prerequisite; not yet stated)

## Sources

- M. H. B. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, University of Copenhagen, May 1998: Definitions 11.7.1 and 11.7.2, Theorem 11.7.3 (Gödel) and Corollary 11.7.4; Section 11.4 for Heyting arithmetic.
