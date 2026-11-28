# Soundness and completeness of BI for Grothendieck resource models

LBI is sound and complete for Grothendieck resource models, with $\bot$ included: a sequent $\Gamma \vdash \varphi$ is provable in LBI if and only if, in every Grothendieck resource model, every world that forces the formula of $\Gamma$ forces $\varphi$.

For every [bunch](formulas-and-bunches-of-bi.md) $\Gamma$ and every BI proposition $\varphi$,

$$
\Gamma \vdash \varphi \ \text{ is provable in LBI} \iff \Gamma \models \varphi ,
$$

where provability is in the sequent calculus [LBI](sequent-calculus-lbi.md) and $\Gamma \models \varphi$ means that for every [Grothendieck resource model](grothendieck-resource-models.md) $\mathcal{G}$ and every world $m$ of $\mathcal{G}$, $m \models \Phi_\Gamma$ implies $m \models \varphi$.

## Depends on

- [Formulas and bunches of BI](formulas-and-bunches-of-bi.md)
- [Grothendieck resource models](grothendieck-resource-models.md)
- [The sequent calculus LBI](sequent-calculus-lbi.md)

## Proof depends on

None.

## Expansion

Missing prerequisites of a proof page, for future pages:

- persistence and the sheaf condition extend from propositional letters to all propositions in Grothendieck resource models (Pym, O'Hearn and Yang, Lemmas 16 and 17; Galmiche, Méry and Pym, remark after Definition 2.9);
- the term model for Grothendieck resource models (Pym, O'Hearn and Yang, Proposition 20, whose worlds are classes of propositions modulo provability of judgements $\varphi \vdash \psi$ between single propositions, as in their Hilbert-type system HBI; the different term model of their Section 5.2, for sheaves over a topological monoid, is the one restricted to normal natural deduction proofs);
- the equivalence of NBI and LBI, or at least that $\Gamma \vdash \varphi$ is provable in LBI exactly when $\Phi_\Gamma \vdash \varphi$ is, to reach the sequent form stated here (Galmiche, Méry and Pym's Theorem 2.5, which gives no proof of its own).

The proof of Pym, O'Hearn and Yang's Lemma 16 uses the Stability condition in the downward orientation, which differs from their printed Definition 12, so that proof cannot be copied verbatim into the upward presentation of [Grothendieck resource models](grothendieck-resource-models.md).

Soundness checks each rule against the sheaf clauses, using that conditions (K) and (Sh) hold for all propositions; the covering conditions handle $\vee$, $\mathrm{I}$ and $\ast$, and Continuity of $J$ handles the multiplicative rules. Completeness builds a term model. In Pym, O'Hearn and Yang's convention (worlds ordered downwards), the worlds are the propositions up to interderivability, $[\varphi] \sqsubseteq [\psi]$ iff $\varphi \vdash \psi$, $[\varphi] \circ [\psi] = [\varphi \ast \psi]$ and $e = [\mathrm{I}]$, and $J([\varphi])$ consists of the finite, possibly empty, families $\{[\varphi_1], \dots, [\varphi_n]\}$ with $\varphi_i \vdash \varphi$ for all $i$ and $\varphi \vdash \varphi_1 \vee \dots \vee \varphi_n$ (the empty disjunction being $\bot$); disjunction and inconsistency are thus handled by the topology, the empty family covering exactly the inconsistent propositions. Pym, O'Hearn and Yang give this proof for judgements between single propositions with their reversed order convention (their Propositions 19 and 20); Galmiche, Méry and Pym state the result for LBI sequents, citing Pym and Pym, O'Hearn and Yang. The term-model construction would be its own page. Unlike the [elementary resource semantics](elementary-resource-semantics-is-incomplete-with-bottom.md), this semantics needs no restriction on $\bot$.

## Sources

- D. Galmiche, D. Méry and D. Pym, "The semantics of BI and resource tableaux", *Mathematical Structures in Computer Science* 15(6) (2005), 1033–1088, <https://doi.org/10.1017/S0960129505004858>; numbering from the author copy read (received 31 March 2005), <https://www.cantab.net/users/david.pym/sem-res-tab.pdf>: Theorem 2.5 (soundness and completeness of BI) and the corollary after it.
- D. J. Pym, P. W. O'Hearn and H. Yang, "Possible worlds and resources: the semantics of BI", *Theoretical Computer Science* 315(1) (2004), 257–305, <https://doi.org/10.1016/j.tcs.2003.11.020>; numbering from the author copy read (dated 29 November 2002), <https://www.cantab.net/users/david.pym/POY-resource-tcs.pdf>: Section 5.3, Proposition 19 (soundness) and Proposition 20 (completeness) with its term model.
