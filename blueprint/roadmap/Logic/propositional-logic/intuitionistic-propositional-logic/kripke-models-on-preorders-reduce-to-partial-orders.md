# Kripke models on preorders reduce to partial orders

Let $(C, \preceq, \Vdash)$ be like a [Kripke model](kripke-models-for-ipc.md) except that $\preceq$ is only a preorder (reflexive and transitive), with forcing of atoms persistent along $\preceq$ and extended to formulas by the same clauses. Let $c \sim c'$ when $c \preceq c'$ and $c' \preceq c$, and order the [classes](../../../SetTheory/sets-functions-relations/quotient-set.md) by $[c] \le [c']$ iff $c \preceq c'$. Then forcing of every formula is constant on classes, $(C/{\sim}, \le, \Vdash)$ with $[c] \Vdash p$ iff $c \Vdash p$ is a Kripke model, and $[c] \Vdash \varphi$ iff $c \Vdash \varphi$ for every formula $\varphi$. So forcing over preorders and over partial orders gives the same consequence relation.

**Proof.** Persistence, proved by induction on formulas exactly as for partial orders, shows that $\sim$-equivalent states force the same formulas; then induction on $\varphi$ compares the two forcing relations, the clause for $\to$ quantifying over the same states.

## Depends on

- [Quotient set](../../../SetTheory/sets-functions-relations/quotient-set.md)
- [Kripke models for intuitionistic propositional logic](kripke-models-for-ipc.md)

## Proof depends on

- [Persistence of forcing in Kripke models](persistence-of-forcing-in-kripke-models.md)

## Sources

- M. H. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, 1998 (published as volume 149 of *Studies in Logic and the Foundations of Mathematics*, Elsevier, 2006), Section 2.5 (Kripke models over partial orders, Definitions 2.5.1 and 2.5.2, and generalized monotonicity).
- J. Moschovakis, *Intuitionistic logic*, Stanford Encyclopedia of Philosophy, substantive revision 16 December 2022, Section 5.1, <https://plato.stanford.edu/entries/logic-intuitionistic/> (Kripke semantics over partially ordered sets). The reduction from preorders is written out here.
