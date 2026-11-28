# Arrow update logic and arbitrary arrow update logic

Arrow update logic models information change by deleting, in a Kripke model, every arrow of an agent that matches none of the clauses of an update; arbitrary arrow update logic adds a modality quantifying over all arrow updates.

**Syntax.** Let $P$ be a countable set of propositional variables and $A$ a finite set of agents. The languages are given by

$$
\varphi ::= p \mid \neg\varphi \mid \varphi \wedge \varphi \mid \Box_a\varphi \mid [U]\varphi \mid [\Uparrow]\varphi, \qquad U ::= (\varphi, a, \varphi) \mid U, (\varphi, a, \varphi),
$$

with $p \in P$ and $a \in A$; an *arrow update* $U$ is a nonempty finite set of *clauses* $(\varphi, a, \varphi')$, as the grammar for $U$ shows. *Arbitrary arrow update logic* AAUL is the full language, and *arrow update logic* AUL its fragment without $[\Uparrow]$. *Arbitrary arrow update logic with common knowledge* AAULC adds a common knowledge operator $C\varphi$, with the usual semantics, and its fragment without $[\Uparrow]$ is AULC.

**Semantics.** Formulas are evaluated on arbitrary Kripke models $M = (W, R, V)$ with an accessibility relation $R(a) \subseteq W \times W$ for each agent. The clauses for $p$, $\neg$, $\wedge$ and $\Box_a$ are the usual ones, and

- $M, w \models [U]\varphi$ iff $M * U, w \models \varphi$, where $M * U = (W, R^U, V)$ keeps exactly the arrows that match a clause: $R^U(a) = \{(v, v') \in R(a) \mid \text{there is } (\varphi, a, \varphi') \in U \text{ with } M, v \models \varphi \text{ and } M, v' \models \varphi'\}$;
- $M, w \models [\Uparrow]\varphi$ iff $M, w \models [U]\varphi$ for every arrow update $U$ of AUL (in AAULC, of AULC).

A formula is satisfiable if it is true at some state of some model, and valid if it is true at every state of every model.

## Depends on

- [Kripke model](../kripke-semantics/kripke-model.md)

## Proof depends on

None.

## Expansion

A clause $(\varphi, a, \varphi')$ reads: if the current state satisfies $\varphi$, then the information given to agent $a$ is compatible with $\varphi'$. Like public announcements, arrow updates give the agents new information; unlike them, the information can differ per agent and depend on the current state. Restricting $[\Uparrow]$ to updates without $[\Uparrow]$ avoids circularity.

## Sources

- H. van Ditmarsch, W. van der Hoek and L. B. Kuijer, "The undecidability of arbitrary arrow update logic", *Theoretical Computer Science* 693:1–12, 2017, <https://doi.org/10.1016/j.tcs.2017.07.018>; read as arXiv:1609.05686v1, <https://arxiv.org/abs/1609.05686v1>: Section 2 (Definitions 1, 2 and 3 and the explanation following them).
- L. B. Kuijer, "Arbitrary arrow update logic with common knowledge is neither RE nor co-RE", in *Proceedings of the Conference on Theoretical Aspects of Rationality and Knowledge (TARK 2017)*, Electronic Proceedings in Theoretical Computer Science 251, 2017, pp. 373–381, <https://doi.org/10.4204/EPTCS.251.27>; read as arXiv:1707.08754v1, <https://arxiv.org/abs/1707.08754v1>: Section 2 (Definitions 1 to 3 and Remark 1, the language with common knowledge).
