# Completeness of the elementary resource semantics without bottom

For the fragment of BI without $\bot$, LBI is complete for elementary Kripke resource models: a $\bot$-free sequent $\Gamma \vdash \varphi$ that is valid in every elementary Kripke resource model is provable in LBI without $\bot$.

If the [bunch](formulas-and-bunches-of-bi.md) $\Gamma$ and the proposition $\varphi$ contain no occurrence of $\bot$, and for every [elementary Kripke resource model](elementary-kripke-resource-models.md) and every world $m$, $m \models \Phi_\Gamma$ gives $m \models \varphi$, then $\Gamma \vdash \varphi$ is provable in [LBI](sequent-calculus-lbi.md) without the rule ($\bot_L$).

## Depends on

- [Formulas and bunches of BI](formulas-and-bunches-of-bi.md)
- [Elementary Kripke resource models](elementary-kripke-resource-models.md)
- [The sequent calculus LBI](sequent-calculus-lbi.md)

## Proof depends on

None.

## Expansion

The converse direction is [soundness](soundness-of-elementary-resource-semantics.md). The restriction to $\bot$-free sequents cannot be dropped: see [incompleteness of the elementary resource semantics with $\bot$](elementary-resource-semantics-is-incomplete-with-bottom.md).

Missing prerequisite of a proof page: the prime-bunch term model of elementary Kripke resource models, which Galmiche, Méry and Pym and Pym, O'Hearn and Yang both attribute to Pym's monograph (not read for this page); Gheorghiu and Pym restate the theorem as previously known, proved by a term-model construction. Pym, O'Hearn and Yang give a simpler Yoneda-style argument for the smaller fragment without both $\bot$ and $\vee$: the propositions form a preordered commutative monoid with $\varphi \sqsubseteq \psi$ iff $\varphi \vdash \psi$, $\varphi \circ \psi = \varphi \ast \psi$ and $e = \mathrm{I}$, in which $\varphi \models \psi$ iff $\varphi \vdash \psi$ (their Proposition 7, with their reversed order convention). That argument fails exactly at $\vee$ and $\bot$; the prime-bunch construction repairs the case of $\vee$.

## Sources

- D. Galmiche, D. Méry and D. Pym, "The semantics of BI and resource tableaux", *Mathematical Structures in Computer Science* 15(6) (2005), 1033–1088, <https://doi.org/10.1017/S0960129505004858>; numbering from the author copy read (received 31 March 2005), <https://www.cantab.net/users/david.pym/sem-res-tab.pdf>: Theorem 2.4 (completeness of BI without $\bot$).
- D. J. Pym, P. W. O'Hearn and H. Yang, "Possible worlds and resources: the semantics of BI", *Theoretical Computer Science* 315(1) (2004), 257–305, <https://doi.org/10.1016/j.tcs.2003.11.020>; numbering from the author copy read (dated 29 November 2002), <https://www.cantab.net/users/david.pym/POY-resource-tcs.pdf>: Proposition 7 (completeness for the $(\bot, \vee)$-free fragment) and the paragraph after it, Section 3.5.
- A. V. Gheorghiu and D. J. Pym, "Semantical analysis of the logic of bunched implications", *Studia Logica* (2023), <https://doi.org/10.1007/s11225-022-10028-z>; read as arXiv:2210.05348v1, <https://arxiv.org/abs/2210.05348v1>: Section 6.2, Theorem 6.3 and the sentence after it.
