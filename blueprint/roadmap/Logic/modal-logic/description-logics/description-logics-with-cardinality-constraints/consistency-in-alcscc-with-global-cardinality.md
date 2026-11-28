# Consistency in ALCSCC++ with an infinite concrete domain that defines equality is undecidable

With global cardinality constraints over the whole domain and feature roles of an infinite concrete domain that can define equality, TBox consistency in ALCSCC++(D) is undecidable.

**Theorem (Baader, Borgwardt, De Bortoli and Koopmann).** If the concrete domain $\mathcal D$ is infinite and JD, then consistency of TBoxes of $\mathcal{ALCSCC}^{++}(\mathcal D)$, the extension of [ALCSCC](the-description-logic-alcscc.md) with sat-restrictions over the whole (finite) domain in which feature roles of $\mathcal D$ may occur as set variables, is undecidable.

Without concrete domains, consistency of $\mathcal{ALCSCC}^{++}$ TBoxes is NEXPTIME-complete. A related result of the same paper: for a numerical concrete domain that is JD, consistency of $\mathcal{ALCOSCC}(\mathcal D)$ TBoxes with mixed numerical constraints, which use feature values directly in the QFBAPA constraints, is undecidable (Theorem 4). For EXPTIME-ω-admissible concrete domains, consistency of $\mathcal{ALCOSCC}(\mathcal D)$, where feature roles are restricted to pairs already connected by a role name, is EXPTIME-complete (Theorem 2).

## Depends on

- [The description logic ALCSCC](the-description-logic-alcscc.md)
- [The description logic ALCSCC++ with global and local cardinality constraints](alcscc-with-global-and-local-cardinality.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)
- [Some multi-stack machine has an undecidable halting set](../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/exists-not-tm2-decidable-tm2-halts-on.md)

## Expansion

The proof reduces Hilbert's tenth problem: sat-restrictions with feature roles simulate multiplication of cardinalities of finite sets. An equation $x = y \cdot z$ is encoded by concept names $A_x, A_y, A_z$ with $|A_x^{\mathcal I}| = |A_y^{\mathcal I}| \cdot |A_z^{\mathcal I}|$: inclusions such as $A_y \equiv \mathrm{sat}(|r_e| \ge 1)$ and $A_y \equiv \mathrm{sat}(r_e = A_z)$ force $r_e^{\mathcal I} = A_y^{\mathcal I} \times A_z^{\mathcal I}$; feature roles $(f_e = \mathit{next}\,g_e)$ and $(g_e = \mathit{next}\,f_e)$, using that $\mathcal D$ is infinite and defines equality, force a role $s_e$ with $|s_e^{\mathcal I}| = |A_x^{\mathcal I}|$; and $\top \sqsubseteq \mathrm{sat}(|r_e| = |s_e|)$ equates the two. Encoding the multiplications of a system of polynomial equations in this way reduces Hilbert's tenth problem, undecidable by the Davis–Putnam–Robinson–Matiyasevich theorem, to consistency.

A good expansion links a page for the encoding of one equation $x = y \cdot z$ by cardinalities of concept names, the lemma that the feature-role constraints force $|s_e^{\mathcal I}| = |A_x^{\mathcal I}|$, and for the reduction of a system of polynomial equations to one ontology.

## Sources

- F. Baader, S. Borgwardt, F. De Bortoli and P. Koopmann, "Concrete Domains Meet Expressive Cardinality Restrictions in Description Logics", in *Automated Deduction – CADE 30*, Lecture Notes in Computer Science 15943, Springer, 2025, pp. 676–695, <https://doi.org/10.1007/978-3-031-99984-0_35>; numbers from the extended version arXiv:2505.21103v1, <https://arxiv.org/abs/2505.21103v1>: Section 6, Theorem 5 and the construction preceding it, Theorem 4, Theorem 2; Appendix C (Corollary 1).
