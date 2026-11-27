# Heyting algebra semantics of intuitionistic propositional logic

A *Heyting algebra* is a lattice $H$ with least element $0$ and greatest element $1$ and a binary operation $\Rightarrow$ such that $c \le a \Rightarrow b$ if and only if $c \cap a \le b$, for all $a, b, c \in H$; then $-a = a \Rightarrow 0$. A Heyting algebra is a distributive lattice, since $c \mapsto c \cap a$ has the right adjoint $a \Rightarrow -$ and so preserves joins. A *valuation* in $H$ maps propositional variables to elements of $H$ and extends to formulas of [IPC](natural-deduction-for-intuitionistic-propositional-logic.md) by $v(\bot) = 0$, $v(\varphi \wedge \psi) = v(\varphi) \cap v(\psi)$, $v(\varphi \vee \psi) = v(\varphi) \cup v(\psi)$ and $v(\varphi \to \psi) = v(\varphi) \Rightarrow v(\psi)$. Write $H, v \models \varphi$ when $v(\varphi) = 1$, and $\Gamma \models \varphi$ when, for every Heyting algebra $H$ and valuation $v$, $H, v \models \varphi$ whenever $H, v \models \psi$ for all $\psi \in \Gamma$.

The open sets of a topological space form a Heyting algebra, with $a \Rightarrow b$ the interior of $(X \setminus a) \cup b$.

## Depends on

- [Natural deduction for intuitionistic propositional logic](natural-deduction-for-intuitionistic-propositional-logic.md)

## Sources

- M. H. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, 1998 (published as volume 149 of *Studies in Logic and the Foundations of Mathematics*, Elsevier, 2006), Section 2.4: Definition 2.4.1 (Heyting algebras), Proposition 2.4.3 (open sets of the plane), Definition 2.4.4 (valuations) and Notation 2.4.5.
