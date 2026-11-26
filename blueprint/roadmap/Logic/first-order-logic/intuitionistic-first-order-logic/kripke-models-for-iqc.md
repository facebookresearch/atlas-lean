# Kripke models for intuitionistic first-order logic

A structure $\mathcal{A}$ is a *substructure* of $\mathcal{B}$, $\mathcal{A} \subseteq \mathcal{B}$, if the domain of $\mathcal{A}$ is contained in that of $\mathcal{B}$, each relation and function of $\mathcal{A}$ is contained in the corresponding one of $\mathcal{B}$, and the constants agree. A *Kripke model* for first-order logic is a triple $\mathcal{C} = (C, \le, \{\mathcal{A}_c\}_{c \in C})$ of a nonempty set $C$, a partial order $\le$ on it and classical structures $\mathcal{A}_c$ with $\mathcal{A}_c \subseteq \mathcal{A}_{c'}$ whenever $c \le c'$, so the domains expand along $\le$.

For a formula $\varphi$ whose free variables are among $\vec{x}$ and a vector $\vec{a}$ of elements of $\mathcal{A}_c$, forcing $c, \vec{a} \Vdash \varphi$ is defined by: atomic formulas hold in $\mathcal{A}_c$ classically; $\bot$ is never forced; $\wedge$, $\vee$ and $\to$ as for [Kripke models of IPC](../../propositional-logic/intuitionistic-propositional-logic/kripke-models-for-ipc.md); $c, \vec{a} \Vdash \exists y\, \varphi$ iff $c, b, \vec{a} \Vdash \varphi$ for some $b$ in $\mathcal{A}_c$; and $c, \vec{a} \Vdash \forall y\, \varphi$ iff $c', b, \vec{a} \Vdash \varphi$ for every $c' \ge c$ and every $b$ in $\mathcal{A}_{c'}$. Write $\Gamma \Vdash \varphi$ when every $c, \vec{a}$ forcing all members of $\Gamma$ forces $\varphi$.

Constant domains, $\mathcal{A}_c$ all with the same domain, validate additional principles and are not this semantics.

## Depends on

- [Kripke models for intuitionistic propositional logic](../../propositional-logic/intuitionistic-propositional-logic/kripke-models-for-ipc.md)

## Sources

- M. H. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, 1998 (published as volume 149 of *Studies in Logic and the Foundations of Mathematics*, Elsevier, 2006), Section 9.4: Definitions 9.4.6 (substructures) and 9.4.7 (Kripke models for first-order logic and forcing).
