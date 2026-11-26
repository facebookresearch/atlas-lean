# Gödel's Dialectica interpretation of Heyting arithmetic

Work in Gödel's quantifier-free theory of [System T](godel-s-system-t.md): its formulas are propositional combinations of equations between terms, its axioms
are the defining equations of the constants (including the recursor), and its rules are substitution, equality, classical propositional logic and induction
on quantifier-free formulas. To each formula $\varphi$ of arithmetic assign by induction a formula $\varphi^D = \exists x\, \forall y\, \varphi_D(x, y)$, where $x$
and $y$ are finite sequences of variables of finite type and $\varphi_D$ is quantifier-free. With $\psi^D = \exists u\, \forall v\, \psi_D(u, v)$:

- for atomic $\varphi$, $x$ and $y$ are empty and $\varphi_D = \varphi$;
- $(\varphi \wedge \psi)^D = \exists x, u\, \forall y, v\, (\varphi_D(x, y) \wedge \psi_D(u, v))$;
- $(\varphi \vee \psi)^D = \exists z, x, u\, \forall y, v\, ((z = 0 \wedge \varphi_D(x, y)) \vee (z = 1 \wedge \psi_D(u, v)))$;
- $(\forall z\, \varphi(z))^D = \exists X\, \forall z, y\, \varphi_D(X z, y, z)$ and $(\exists z\, \varphi(z))^D = \exists z, x\, \forall y\, \varphi_D(x, y, z)$;
- $(\varphi \to \psi)^D = \exists U, Y\, \forall x, v\, (\varphi_D(x, Y x v) \to \psi_D(U x, v))$, so that, with $\neg \varphi = \varphi \to \bot$,
  $(\neg \varphi)^D = \exists Y\, \forall x\, \neg \varphi_D(x, Y x)$.

**Theorem (Gödel).** If Heyting arithmetic proves $\varphi$, then there is a sequence of terms $t$ such that the theory of System T proves $\varphi_D(t, y)$.
Since the interpretation is syntactic, a weak base theory proves that the consistency of the theory of System T implies the consistency of Heyting
arithmetic.

## Depends on

- [Gödel's System T](godel-s-system-t.md)
- [Heyting arithmetic](../../../Logic/proof-theory/heyting-arithmetic/heyting-arithmetic.md)

## Sources

- J. Avigad and S. Feferman, "Gödel's functional (“Dialectica”) interpretation", in S. R. Buss (ed.), *Handbook of Proof Theory*, Studies in Logic and the Foundations of Mathematics 137, Elsevier, 1998, pp. 337–405, <https://doi.org/10.1016/S0049-237X(98)80020-7>: Section 2.2 (the theory T: terms, the defining equations of the recursors, axioms and the quantifier-free induction rule), Section 2.3 (clauses 1–7 of the D-interpretation), Theorem 2.4.1 and Theorem 3.2.1 (relative consistency).
- M. H. B. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, University of Copenhagen, May 1998: Definitions 11.7.1 and 11.7.2, Theorem 11.7.3 (Gödel) and Corollary 11.7.4, a variant that uses boolean terms and product types in place of quantifier-free formulas and sequences of variables; Section 11.4 for Heyting arithmetic.
