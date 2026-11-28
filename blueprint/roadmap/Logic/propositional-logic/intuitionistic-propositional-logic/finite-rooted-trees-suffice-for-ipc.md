# Finite rooted trees suffice for intuitionistic propositional logic

A formula $\varphi$ of intuitionistic propositional logic is derivable without premises in [natural deduction for IPC](natural-deduction-for-intuitionistic-propositional-logic.md) if and only if it is forced at the root of every [Kripke model](kripke-models-for-ipc.md) whose set of states, ordered by $\le$, is a finite tree with a least element, its root.

For example, the model with states $k < k'$ and $k < k''$, with $P$ forced only at $k'$, shows that neither $P \vee \neg P$ nor $\neg P \vee \neg\neg P$ is derivable.

## Depends on

- [Natural deduction for intuitionistic propositional logic](natural-deduction-for-intuitionistic-propositional-logic.md)
- [Kripke models for intuitionistic propositional logic](kripke-models-for-ipc.md)

## Proof depends on

- [Kripke soundness of intuitionistic propositional logic](kripke-soundness-of-ipc.md)

## Expansion

The direction from derivability to forcing is Kripke soundness. The converse needs prerequisites that have no pages yet, each a proof prerequisite: a finite countermodel for an underivable formula (the finite model property, for instance by a canonical model built from prime theories over the subformulas of $\varphi$, or by filtration), and the unravelling of a finite rooted partial order into a finite tree, together with the fact that it preserves forcing at the root.

## Sources

- J. Moschovakis, *Intuitionistic logic*, Stanford Encyclopedia of Philosophy, substantive revision 16 December 2022, <https://plato.stanford.edu/entries/logic-intuitionistic/>, Section 5.1: an arbitrary propositional formula is intuitionistically provable if and only if it is forced by the root of every Kripke model whose frame is a finite tree with a least element, and the example with three nodes.
