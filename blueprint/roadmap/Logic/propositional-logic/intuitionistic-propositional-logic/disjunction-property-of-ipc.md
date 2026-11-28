# Disjunction property of intuitionistic propositional logic

If $\vdash \varphi \vee \psi$ in [natural deduction for IPC](natural-deduction-for-intuitionistic-propositional-logic.md), then $\vdash \varphi$ or $\vdash \psi$.

**Proof.** Suppose neither. By [completeness](kripke-completeness-of-ipc.md) there are [Kripke models](kripke-models-for-ipc.md) with states $c_1$ and $c_2$ such that $c_1 \nVdash \varphi$ and $c_2 \nVdash \psi$; restricting each model to the states above $c_1$, respectively $c_2$, leaves forcing at those states unchanged, by induction on formulas, since forcing at a state looks only at states above it, and gives models $\mathcal{C}_1$, $\mathcal{C}_2$ with least states $c_1, c_2$. Put the disjoint union of the two models above a new least state $c_0$ forcing no variable. Forcing at states of each part is unchanged. By [soundness](kripke-soundness-of-ipc.md), $c_0 \Vdash \varphi \vee \psi$, so $c_0$ forces $\varphi$ or $\psi$, and by [persistence](persistence-of-forcing-in-kripke-models.md) so does $c_1$ or $c_2$ respectively, a contradiction.

## Depends on

- [Natural deduction for intuitionistic propositional logic](natural-deduction-for-intuitionistic-propositional-logic.md)

## Proof depends on

- [Kripke models for intuitionistic propositional logic](kripke-models-for-ipc.md)
- [Kripke soundness of intuitionistic propositional logic](kripke-soundness-of-ipc.md)
- [Kripke completeness of intuitionistic propositional logic](kripke-completeness-of-ipc.md)
- [Persistence of forcing in Kripke models](persistence-of-forcing-in-kripke-models.md)

## Sources

- M. H. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, 1998 (published as volume 149 of *Studies in Logic and the Foundations of Mathematics*, Elsevier, 2006), Section 2.5: Proposition 2.5.7 and its proof.
