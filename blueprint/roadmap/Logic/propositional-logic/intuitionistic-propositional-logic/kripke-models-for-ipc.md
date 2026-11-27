# Kripke models for intuitionistic propositional logic

A *Kripke model* is a triple $\mathcal{C} = (C, \le, \Vdash)$ of a nonempty set $C$ of states, a [partial order](../../../Order/ordered-sets/partial-order.md) $\le$ on $C$ and a relation $\Vdash$ between states and propositional variables that is *persistent*: if $c \le c'$ and $c \Vdash p$, then $c' \Vdash p$. Forcing extends to all formulas of [IPC](natural-deduction-for-intuitionistic-propositional-logic.md):

- $c \Vdash \bot$ never holds;
- $c \Vdash \varphi \wedge \psi$ iff $c \Vdash \varphi$ and $c \Vdash \psi$;
- $c \Vdash \varphi \vee \psi$ iff $c \Vdash \varphi$ or $c \Vdash \psi$;
- $c \Vdash \varphi \to \psi$ iff $c' \Vdash \psi$ for every $c' \ge c$ with $c' \Vdash \varphi$.

Hence $c \Vdash \neg\varphi$ iff no $c' \ge c$ forces $\varphi$. Write $\mathcal{C} \Vdash \varphi$ when every state forces $\varphi$, and $\mathcal{C} \Vdash \Gamma$ when $\mathcal{C} \Vdash \psi$ for all $\psi \in \Gamma$.

## Depends on

- [Partial order](../../../Order/ordered-sets/partial-order.md)
- [Natural deduction for intuitionistic propositional logic](natural-deduction-for-intuitionistic-propositional-logic.md)

## Sources

- M. H. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, 1998 (published as volume 149 of *Studies in Logic and the Foundations of Mathematics*, Elsevier, 2006), Section 2.5: Definitions 2.5.1 and 2.5.2 and the derived clause for negation.
