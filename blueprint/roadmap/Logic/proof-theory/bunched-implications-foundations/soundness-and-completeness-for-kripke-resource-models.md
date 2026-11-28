# Soundness and completeness of BI for Kripke resource models with an inconsistent world

BI is sound and complete for Kripke resource models with an inconsistent world: a proposition $\varphi$, possibly containing $\bot$, is a theorem of BI if and only if the unit world $e$ forces $\varphi$ in every preordered commutative monoid model whose greatest element $\pi$ absorbs composition and alone forces $\bot$.

For every BI proposition $\varphi$,

$$
\emptyset_m \vdash \varphi \ \text{ is provable in LBI} \iff e \models \varphi \text{ in every Kripke resource model with an inconsistent world},
$$

where provability is in [LBI](sequent-calculus-lbi.md) (so the left side says that $\varphi$ is a theorem of BI) and the models are those of [Kripke resource models with an inconsistent world](kripke-resource-models-with-inconsistency.md), with $e$ the unit of the monoid. Since forcing is upward closed and $m \models \mathrm{I}$ exactly when $e \sqsubseteq m$, the right side says equivalently that every world forcing $\mathrm{I}$ forces $\varphi$.

## Depends on

- [Kripke resource models with an inconsistent world](kripke-resource-models-with-inconsistency.md)
- [The sequent calculus LBI](sequent-calculus-lbi.md)

## Proof depends on

None.

## Expansion

Missing prerequisites of a proof page, for future pages:

- BI frames and soundness of LBI for the ternary relational semantics (Galmiche, Méry and Pym, Definitions 5.1 to 5.3 and Theorem 5.1);
- the resource tableau calculus TBI with its completeness and countermodel extraction (their Theorem 4.3 and Definition 4.6), the main technical step;
- basic Grothendieck resource models coincide with Kripke resource models with an inconsistent world (their Lemma 5.6).

Galmiche, Méry and Pym prove soundness for a ternary relational semantics (BI frames with a greatest element $\pi$) by checking that each LBI rule preserves validity of sequents, and note that Kripke resource models are the instance $R xyz \Leftrightarrow x \bullet y \sqsubseteq z$. For completeness they build a counter-model from an unprovable sequent through their labelled resource tableaux: a complete open tableau branch yields a basic [Grothendieck resource model](grothendieck-resource-models.md) refuting the sequent, and basic Grothendieck resource models coincide with Kripke resource models with an inconsistent world. The same soundness and completeness hold for the equivalent partially defined monoid (PDM) models (their Theorems 5.8 and 5.9), which makes BI complete for a class of partial resource models containing the heap models of separation logic. In contrast, the [elementary resource semantics](elementary-resource-semantics-is-incomplete-with-bottom.md), with no inconsistent world, is incomplete in the presence of $\bot$.

## Sources

- D. Galmiche, D. Méry and D. Pym, "The semantics of BI and resource tableaux", *Mathematical Structures in Computer Science* 15(6) (2005), 1033–1088, <https://doi.org/10.1017/S0960129505004858>; numbering from the author copy read (received 31 March 2005), <https://www.cantab.net/users/david.pym/sem-res-tab.pdf>: Section 5.1, Theorem 5.1 (soundness for the relational semantics) and Theorem 5.2 (completeness for it); Section 5.2, Theorem 5.3 (soundness of BI with respect to Kripke resource models), Lemma 5.6 and Theorem 5.7 (completeness of BI with respect to Kripke resource models); Section 5.3, Theorems 5.8 and 5.9; Corollary 2.1 (theorems are the propositions $\varphi$ with $\emptyset_m \vdash \varphi$ provable) and the corollary after Theorem 2.5 (validity of a proposition as forcing at $e$).
