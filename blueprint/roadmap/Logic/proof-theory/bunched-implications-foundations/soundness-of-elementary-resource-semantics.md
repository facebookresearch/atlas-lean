# Soundness of LBI for elementary Kripke resource models

The sequent calculus LBI is sound for elementary Kripke resource models: every provable sequent $\Gamma \vdash \varphi$, possibly containing $\bot$, is valid, so every world that forces the formula of $\Gamma$ forces $\varphi$.

For every [bunch](formulas-and-bunches-of-bi.md) $\Gamma$ and BI proposition $\varphi$, if $\Gamma \vdash \varphi$ is provable in [LBI](sequent-calculus-lbi.md), then $\Gamma \models \varphi$: for every [elementary Kripke resource model](elementary-kripke-resource-models.md) and every world $m$ of it, $m \models \Phi_\Gamma$ gives $m \models \varphi$, where $\Phi_\Gamma$ is the formula of $\Gamma$.

## Depends on

- [Elementary Kripke resource models](elementary-kripke-resource-models.md)
- [The sequent calculus LBI](sequent-calculus-lbi.md)

## Proof depends on

None.

## Expansion

The proof checks that each LBI rule preserves validity, by induction on derivations. It uses persistence of forcing along $\sqsubseteq$ (condition (K) extended from letters to all propositions by induction, as noted on the models page) for the additive implication, and bifunctoriality of $\bullet$ for the multiplicative rules; the rule ($\bot_L$) is valid because $\bot$ is forced at no world. Galmiche, Méry and Pym state the theorem and cite Pym's monograph and Pym, O'Hearn and Yang for it; Pym, O'Hearn and Yang prove it (their Lemma 5) for judgements between single propositions with their reversed order convention, by a straightforward induction on proofs. The converse holds only for the fragment without $\bot$: see [completeness of the elementary resource semantics without bottom](completeness-of-elementary-resource-semantics-without-bottom.md) and [incompleteness with bottom](elementary-resource-semantics-is-incomplete-with-bottom.md).

## Sources

- D. Galmiche, D. Méry and D. Pym, "The semantics of BI and resource tableaux", *Mathematical Structures in Computer Science* 15(6) (2005), 1033–1088, <https://doi.org/10.1017/S0960129505004858>; numbering from the author copy read (received 31 March 2005), <https://www.cantab.net/users/david.pym/sem-res-tab.pdf>: Section 2.1, Theorem 2.3 (soundness of BI) and the definition of validity after Definition 2.5.
- D. J. Pym, P. W. O'Hearn and H. Yang, "Possible worlds and resources: the semantics of BI", *Theoretical Computer Science* 315(1) (2004), 257–305, <https://doi.org/10.1016/j.tcs.2003.11.020>; numbering from the author copy read (dated 29 November 2002), <https://www.cantab.net/users/david.pym/POY-resource-tcs.pdf>: Section 3.4, Lemma 5 (soundness) and its proof sketch.
