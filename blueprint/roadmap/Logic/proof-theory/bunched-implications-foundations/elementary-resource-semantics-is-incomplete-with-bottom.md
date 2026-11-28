# Incompleteness of the elementary resource semantics with bottom

With $\bot$ forced at no world, the elementary Kripke resource semantics is incomplete for BI: for distinct propositional letters $p$ and $q$, a sequent built from $p$, $q$, $\ast$, $\mathrel{-\!\!\ast}$, $\wedge$, $\to$ and $\bot$ holds in every elementary model but is not provable in BI.

For distinct propositional letters $p, q$ let

$$
\Gamma = \bigl((p \mathrel{-\!\!\ast} \bot) \to \bot\bigr) \wedge \bigl((q \mathrel{-\!\!\ast} \bot) \to \bot\bigr), \qquad \chi = \bigl((p \ast q) \mathrel{-\!\!\ast} \bot\bigr) \to \bot .
$$

Then $m \models \Gamma$ implies $m \models \chi$ for every world $m$ of every [elementary Kripke resource model](elementary-kripke-resource-models.md), so $\Gamma \models \chi$, but $\Gamma \vdash \chi$ is not provable in [LBI](sequent-calculus-lbi.md).

## Depends on

- [Elementary Kripke resource models](elementary-kripke-resource-models.md)
- [The sequent calculus LBI](sequent-calculus-lbi.md)

## Proof depends on

- [Cut elimination for LBI](cut-elimination-for-lbi.md)

## Expansion

Validity: since $\bot$ is forced nowhere, $m \models \varphi \mathrel{-\!\!\ast} \bot$ holds exactly when no world forces $\varphi$, independently of $m$; hence $m \models (\varphi \mathrel{-\!\!\ast} \bot) \to \bot$ holds exactly when some world forces $\varphi$. If some $n$ forces $p$ and some $n'$ forces $q$, then $n \bullet n'$ forces $p \ast q$, because the monoid operation is total; so $\Gamma$ forces $\chi$. Unprovability: the formula $p \ast (p \mathrel{-\!\!\ast} \bot)$ entails $\bot$ in BI although $p$ and $p \mathrel{-\!\!\ast} \bot$ are each consistent, and Pym, O'Hearn and Yang establish that $\Gamma \vdash \chi$ has no derivation via the cut-elimination theorem for the sequent calculus; they also give an explicit counter-model among their Grothendieck sheaf models. The incompleteness is what motivates the [Grothendieck resource models](grothendieck-resource-models.md) and the [resource models with an inconsistent world](kripke-resource-models-with-inconsistency.md), in which $\bot$ is forced at some worlds. Pym, O'Hearn and Yang state the result with the opposite order convention, which does not affect it: the argument above uses no property of the order.

## Sources

- D. J. Pym, P. W. O'Hearn and H. Yang, "Possible worlds and resources: the semantics of BI", *Theoretical Computer Science* 315(1) (2004), 257–305, <https://doi.org/10.1016/j.tcs.2003.11.020>; numbering from the author copy read (dated 29 November 2002), <https://www.cantab.net/users/david.pym/POY-resource-tcs.pdf>: Section 3.5, Proposition 6 (elementary incompleteness) and its proof.
- D. Galmiche, D. Méry and D. Pym, "The semantics of BI and resource tableaux", *Mathematical Structures in Computer Science* 15(6) (2005), 1033–1088, <https://doi.org/10.1017/S0960129505004858>; numbering from the author copy read (received 31 March 2005), <https://www.cantab.net/users/david.pym/sem-res-tab.pdf>: Section 2.1, the paragraph after Theorem 2.4 (incompleteness arises from the interaction of $\mathrel{-\!\!\ast}$ and $\bot$).
