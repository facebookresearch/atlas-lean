# Soundness and completeness of IPC for Heyting algebras

For every set $\Gamma$ of formulas and formula $\varphi$ of intuitionistic propositional logic, $\Gamma \vdash \varphi$ in [natural deduction](natural-deduction-for-intuitionistic-propositional-logic.md) if and only if $\Gamma \models \varphi$ in the [Heyting algebra semantics](heyting-algebra-semantics-of-ipc.md).

**Proof sketch.** Soundness by induction on derivations. For completeness, the formulas modulo provable equivalence relative to $\Gamma$ form a Heyting algebra, the Lindenbaum algebra $L_\Gamma$; under the valuation $v(p) = [p]$ every formula $\psi$ has the value $[\psi]$, and $[\varphi] = 1$ only when $\Gamma \vdash \varphi$.

## Depends on

- [Natural deduction for intuitionistic propositional logic](natural-deduction-for-intuitionistic-propositional-logic.md)
- [Heyting algebra semantics of intuitionistic propositional logic](heyting-algebra-semantics-of-ipc.md)

## Sources

- M. H. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, 1998 (published as volume 149 of *Studies in Logic and the Foundations of Mathematics*, Elsevier, 2006), Section 2.4: Theorem 2.4.6 (soundness and completeness) and the construction of the Lindenbaum algebra before it.
