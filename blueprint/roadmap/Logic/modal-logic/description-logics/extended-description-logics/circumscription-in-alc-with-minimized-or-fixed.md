# Circumscription in ALC with minimized or fixed roles is undecidable

Reasoning with circumscribed ALC knowledge bases, decidable when only concept names are minimized or fixed, becomes undecidable as soon as role names are minimized, and at least as hard as monadic second-order consequence when role names are fixed.

**Theorem (Bonatti, Lutz and Wolter).** For [circumscribed knowledge bases](circumscribed-description-logic-knowledge-bases.md):

1. in ALC, satisfiability with respect to role-minimizing cKBs is undecidable (Theorem 28 of the source);
2. in ALCI, the extension of ALC by inverse roles $r^-$ interpreted as the converse relation $\{(e, d) \mid (d, e) \in r^{\mathcal I}\}$, satisfiability with respect to role-minimizing cKBs with empty TBox is undecidable (Theorem 30);
3. the logical consequence problem of monadic second-order logic with one binary relation symbol $r$ (MSO($r$): first-order logic over the signature $\{r\}$ extended with quantification over sets of elements), over unrestricted structures, is effectively reducible to the instance problem with respect to role-fixing cKBs formulated in ALC, even when the TBox and the preference relation are empty (Theorem 22).

By contrast, in ALCIO and ALCQO instance checking, satisfiability and subsumption with respect to concept-circumscribed knowledge bases, in which only concept names are minimized or fixed, are decidable (NEXP$^{\mathrm{NP}}$-complete), and for role-minimizing cKBs with empty TBox reasoning is decidable (again NEXP$^{\mathrm{NP}}$-complete) for the description logics between ALC and ALCQO; according to the source's introduction, adding acyclic TBoxes already makes these logics undecidable. The source concludes from part 3 that reasoning with role-fixing cKBs in ALC, already with one fixed role name and empty TBox, is outside the analytic hierarchy.

## Depends on

- [Circumscribed description logic knowledge bases](circumscribed-description-logic-knowledge-bases.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

*Parts 1 and 2.* The proof reduces the tiling problem for the quadrant $\mathbb N \times \mathbb N$ (Definition 26): for a tiling problem $P$ a role-minimizing cKB in ALC is built such that a concept is satisfiable with respect to it iff $P$ has a solution. For ALCI with empty TBox, the "spy-point" technique of Areces, Blackburn and Marx lets an ABox with inverse roles simulate the TBox. A good expansion links the undecidability of tiling the quadrant $\mathbb N \times \mathbb N$.

*Part 3.* Thomason's effective translation of monadic second-order sentences with a binary relation $r$ into ALC concepts (Theorem 20) reduces consequence in MSO($r$) to semantic consequence of modal logic over frames; Lemma 21 (using the universal role) and Theorem 22 then reduce this to the instance problem for role-fixing cKBs in ALC, even with empty TBox and preference relation; a good expansion links the undecidability of consequence in monadic second-order logic with a binary relation.

## Sources

- P. A. Bonatti, C. Lutz and F. Wolter, "The complexity of circumscription in DLs", *Journal of Artificial Intelligence Research* 35:717–773, 2009, <https://doi.org/10.1613/jair.2763>; read as arXiv:1401.3476v1, <https://arxiv.org/abs/1401.3476v1>: Section 1 (summary of results), Section 5 (Definition 19, Theorems 20 and 22) and Section 6 (Definitions 23 and 26, Theorems 28 and 30).
