# Soundness of LBI for Kripke resource models with an inconsistent world

The sequent calculus LBI is sound for Kripke resource models with an inconsistent world: for every provable sequent $\Gamma \vdash \varphi$, possibly containing $\bot$, every world that forces the formula of $\Gamma$ forces $\varphi$, in every preordered commutative monoid model whose greatest element $\pi$ absorbs composition and alone forces $\bot$.

For every [bunch](formulas-and-bunches-of-bi.md) $\Gamma$ and BI proposition $\varphi$, if $\Gamma \vdash \varphi$ is provable in [LBI](sequent-calculus-lbi.md), then for every [Kripke resource model with an inconsistent world](kripke-resource-models-with-inconsistency.md) and every world $m$ of it, $m \models \Phi_\Gamma$ gives $m \models \varphi$, where $\Phi_\Gamma$ is the formula of $\Gamma$. In particular, every theorem $\varphi$ of BI, one with $\emptyset_m \vdash \varphi$ provable, is forced at the unit $e$ of every such model.

## Depends on

- [Formulas and bunches of BI](formulas-and-bunches-of-bi.md)
- [Kripke resource models with an inconsistent world](kripke-resource-models-with-inconsistency.md)
- [The sequent calculus LBI](sequent-calculus-lbi.md)

## Proof depends on

None.

## Expansion

The proof checks that each LBI rule preserves validity, by induction on derivations. It uses that forcing is upward closed and that every world above $\pi$ forces every proposition, both by induction on propositions as noted on the models page; bifunctoriality of $\bullet$ for the multiplicative rules; and, for ($\bot_L$), that a world forcing $\Phi_{\Gamma(\bot)}$ lies above $\pi$: by induction on the context $\Gamma(-)$, a world forcing $\chi \ast \Phi$ or $\chi \wedge \Phi$ with $\Phi$ forced only above $\pi$ is itself above $\pi$, because $n \bullet n' \sqsubseteq m$ with $\pi \sqsubseteq n'$ gives $\pi = n \bullet \pi \sqsubseteq n \bullet n' \sqsubseteq m$. Galmiche, Méry and Pym state the theorem (their Theorem 5.3) and obtain it from soundness of LBI for their ternary relational semantics (their Theorem 5.1), of which these models are the instance $R xyz \Leftrightarrow x \bullet y \sqsubseteq z$. It also follows from [soundness and completeness for Grothendieck resource models](soundness-and-completeness-for-grothendieck-resource-models.md), whose soundness half is stated for every Grothendieck resource model, together with their Lemma 5.6, that these models are exactly the basic Grothendieck resource models.

The converse, completeness, is not stated here. Galmiche, Méry and Pym's completeness theorems for these models and for the equivalent partially defined monoid (PDM) models (their Theorems 5.7 and 5.9) are proved through the resource tableau calculus TBI (their Theorem 4.3), and Pym's 2025 summary of the completeness literature states that the results for the KRM and PDM semantics are correct for the tableau calculus TBI, while some places in that paper write BI for TBI, possibly implying results, for instance for LBI, that are not obtained there. The tableau results belong to [relational semantics and resource tableaux for BI](relational-semantics-and-resource-tableaux-for-bi.md). By contrast, the [Grothendieck resource models](grothendieck-resource-models.md), of which these are the basic ones, are complete for LBI.

## Sources

- D. Galmiche, D. Méry and D. Pym, "The semantics of BI and resource tableaux", *Mathematical Structures in Computer Science* 15(6) (2005), 1033–1088, <https://doi.org/10.1017/S0960129505004858>; numbering from the author copy read (received 31 March 2005), <https://www.cantab.net/users/david.pym/sem-res-tab.pdf>: Section 5.1, Theorem 5.1 (soundness for the relational semantics); Section 5.2, Theorem 5.3 (soundness with respect to Kripke resource models), Lemma 5.6 and Theorem 5.7 with its proof; Section 5.3, Theorems 5.8 and 5.9; Section 2.2, Theorem 2.5.
- D. Pym, "A summary of the more recent papers on the completeness of the Logic of Bunched Implications", dated 2 November 2025, <https://www.cantab.net/users/david.pym/BI-completeness-papers.pdf>: item 4.
