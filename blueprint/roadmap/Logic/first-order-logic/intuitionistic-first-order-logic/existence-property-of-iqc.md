# Existence property of intuitionistic first-order logic

If $\vdash \exists x\, \varphi$ in [natural deduction for IQC](natural-deduction-for-intuitionistic-first-order-logic.md), then $\vdash \varphi[x := t]$ for some term $t$.

The source derives it from cut elimination for the intuitionistic sequent calculus: the last rule of a cut-free proof of $\vdash \exists x\, \varphi$ is ($\exists$R), whose premise is $\vdash \varphi[x := t]$.

## Depends on

- [Natural deduction for intuitionistic first-order logic](natural-deduction-for-intuitionistic-first-order-logic.md)

## Sources

- M. H. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, 1998 (published as volume 149 of *Studies in Logic and the Foundations of Mathematics*, Elsevier, 2006), Section 9.3: Theorem 9.3.1 (cut elimination) and Corollary 9.3.2 (existence property).
