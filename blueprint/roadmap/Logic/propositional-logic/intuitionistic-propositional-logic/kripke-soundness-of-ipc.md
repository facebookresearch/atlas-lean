# Kripke soundness of intuitionistic propositional logic

If $\Gamma \vdash \varphi$ in [natural deduction for IPC](natural-deduction-for-intuitionistic-propositional-logic.md), then every [Kripke model](kripke-models-for-ipc.md) $\mathcal{C}$ with $\mathcal{C} \Vdash \Gamma$ satisfies $\mathcal{C} \Vdash \varphi$. More precisely, every state that forces all members of $\Gamma$ forces $\varphi$.

**Proof.** By induction on the derivation, using [persistence](persistence-of-forcing-in-kripke-models.md) in the case of ($\to$I): if $c$ forces $\Gamma$ and $c' \ge c$ forces $\varphi$, then $c'$ forces $\Gamma, \varphi$ and so $\psi$.

## Depends on

- [Natural deduction for intuitionistic propositional logic](natural-deduction-for-intuitionistic-propositional-logic.md)
- [Kripke models for intuitionistic propositional logic](kripke-models-for-ipc.md)

## Proof depends on

- [Persistence of forcing in Kripke models](persistence-of-forcing-in-kripke-models.md)

## Sources

- M. H. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, 1998 (published as volume 149 of *Studies in Logic and the Foundations of Mathematics*, Elsevier, 2006), Section 2.5: Theorem 2.5.6, the left-to-right part, proved by induction (Exercise 2.7.13).
