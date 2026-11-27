# Existence property of intuitionistic first-order logic

If $\vdash \exists x\, \varphi$ in [natural deduction for IQC](natural-deduction-for-intuitionistic-first-order-logic.md), then $\vdash \varphi[x := t]$ for some term $t$.

**Proof idea.** Natural deduction and the intuitionistic sequent calculus LJ derive the same sequents, so $\vdash \exists x\, \varphi$ has an LJ proof, and by cut elimination a cut-free one. The last rule of a cut-free LJ proof of $\vdash \exists x\, \varphi$ is ($\exists$R), whose premise $\vdash \varphi[x := t]$ gives a natural deduction proof back.

## Depends on

- [Natural deduction for intuitionistic first-order logic](natural-deduction-for-intuitionistic-first-order-logic.md)

## Proof depends on

- [Cut elimination for the intuitionistic sequent calculus LJ](../../proof-theory/cut-elimination-for-the-intuitionistic-sequent-calculus.md)

## Sources

- M. H. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, 1998 (published as volume 149 of *Studies in Logic and the Foundations of Mathematics*, Elsevier, 2006), Section 9.3: Theorem 9.3.1 (cut elimination), Corollary 9.3.2 (existence property) and Theorem 9.3.6 (natural deduction, sequent calculus and the Hilbert system are equivalent).

## Expansion

This page becomes ready once this prerequisite is stated:

- the equivalence of natural deduction for intuitionistic first-order logic with the sequent calculus LJ, in both directions and for sequents with free variables (Sørensen–Urzyczyn, Theorem 9.3.6), a proof prerequisite.
