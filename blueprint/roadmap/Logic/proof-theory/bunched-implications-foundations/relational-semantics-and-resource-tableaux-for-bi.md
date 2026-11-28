# Relational semantics and resource tableaux for BI

This node covers the ternary relational semantics of BI and the labelled resource tableau calculus TBI, with which Galmiche, Méry and Pym relate the Grothendieck, inconsistent-world and partially defined monoid semantics.

Galmiche, Méry and Pym define BI frames, sets of resources with a ternary relation and a greatest element $\pi$, relational interpretations and relational models, prove soundness of BI for them (their Theorem 5.1) and completeness through a term model of prime bunches (their Theorem 5.2), and obtain [Kripke resource models with an inconsistent world](kripke-resource-models-with-inconsistency.md) as the instance $R xyz \Leftrightarrow x \bullet y \sqsubseteq z$. Their tableau calculus TBI works with signed formulas labelled by words of a labelling language and with constraints between labels interpreted in a preordered commutative monoid; a closed tableau sequence is a TBI proof. They prove soundness of TBI with respect to basic [Grothendieck resource models](grothendieck-resource-models.md) (their Theorem 4.1), completeness of TBI by extracting a basic Grothendieck resource model from a complete open branch (their Theorem 4.3), and soundness and completeness of TBI with respect to Kripke resource models with an inconsistent world (their Theorems 5.4 and 5.5), using that these coincide with the basic Grothendieck resource models (their Lemma 5.6). Pym's 2025 summary of the completeness literature states that the results of that paper for the KRM and PDM semantics are correct for the tableau calculus TBI, that in some places it writes BI for TBI, possibly implying results, for instance for LBI, that are not obtained, and that its claim of decidability is not substantiated. Gheorghiu and Pym (2023) give a general treatment of completeness for the ternary relational semantics and discuss the variants with an inconsistent world and with partial or non-deterministic monoids.

## Depends on

- [The sequent calculus LBI](sequent-calculus-lbi.md)
- [Grothendieck resource models](grothendieck-resource-models.md)
- [Kripke resource models with an inconsistent world](kripke-resource-models-with-inconsistency.md)

## Proof depends on

None.

## Expansion

This node is still to expand. A good expansion states BI frames and relational models, relational soundness and completeness, the calculus TBI with its notions of closure and proof, and soundness and completeness of TBI for basic Grothendieck resource models and for Kripke resource models with an inconsistent world, each on its own page and each as its source states it, distinguishing results for TBI from results for LBI.

## Sources

- D. Galmiche, D. Méry and D. Pym, "The semantics of BI and resource tableaux", *Mathematical Structures in Computer Science* 15(6) (2005), 1033–1088, <https://doi.org/10.1017/S0960129505004858>; numbering from the author copy read (received 31 March 2005), <https://www.cantab.net/users/david.pym/sem-res-tab.pdf>: Section 3 (labels, constraints and TBI, Definitions 3.1 to 3.9), Section 4 (Lemma 4.2, Theorem 4.1, Definition 4.6 and Theorem 4.3), Section 5.1 (Definitions 5.1 to 5.4 and Theorems 5.1 and 5.2) and Section 5.2 (Lemma 5.6 and Theorems 5.4 and 5.5).
- D. Pym, "A summary of the more recent papers on the completeness of the Logic of Bunched Implications", dated 2 November 2025, <https://www.cantab.net/users/david.pym/BI-completeness-papers.pdf>: item 4.
- A. V. Gheorghiu and D. J. Pym, "Semantical analysis of the logic of bunched implications", *Studia Logica* (2023), <https://doi.org/10.1007/s11225-022-10028-z>; read as arXiv:2210.05348v1, <https://arxiv.org/abs/2210.05348v1>: Section 6 (the monoid, consistency and inconsistency semantics, and partial and non-deterministic monoids).
