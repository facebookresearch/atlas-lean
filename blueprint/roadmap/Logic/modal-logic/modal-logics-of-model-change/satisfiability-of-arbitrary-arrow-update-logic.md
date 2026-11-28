# Satisfiability of arbitrary arrow update logic is co-r.e.-hard

The satisfiability problem of arbitrary arrow update logic is co-r.e.-hard, hence undecidable, and with common knowledge neither the valid nor the satisfiable formulas are recursively enumerable.

**Theorem (van Ditmarsch, van der Hoek and Kuijer; Kuijer).** For the logics of the page on [arrow update logics](arrow-update-logic-and-arbitrary-arrow-update.md):

1. for a set of at least six agents, the satisfiability problem of AAUL is co-r.e.-hard, and therefore undecidable (Theorem 1 of the journal paper);
2. for a set of at least five agents, the set of valid formulas of AAULC is neither recursively enumerable nor co-recursively enumerable (Corollary 1 of the conference paper), so AAULC has no finitary axiomatization (Corollary 2).

Whether the satisfiability problem of AAUL is itself co-recursively enumerable is open in the journal paper. The thresholds on the number of agents are the assumptions under which the sources carry out their proofs; the conference paper remarks that its proof could be modified to use one agent.

## Depends on

- [Arrow update logic and arbitrary arrow update logic](arrow-update-logic-and-arbitrary-arrow-update.md)
- [Recognizability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-recognizable.md)
- [Co-recognizability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-co-recognizable.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The tiling problem is undecidable](../../../TheoryOfComputation/undecidable-problems/wang-tiles/the-tiling-problem-is-undecidable.md)
- [The halting problem for single-tape machines is undecidable](../../../TheoryOfComputation/computability/halting-problem-for-single-tape-turing-machines/exists-not-tm2-decidable-tm0-halts-on.md)
- [The halting problem is not co-recognizable by multi-stack machines](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-co-recognizable-halting.md)

## Expansion

*Part 1.* The proof reduces the tiling problem for the plane $\mathbb Z \times \mathbb Z$: for every finite set of tile types it builds an AAUL formula that is satisfiable iff the tile types can tile the plane, representing each point of $\mathbb Z \times \mathbb Z$ by a state. Since the tiling problem is co-r.e.-complete, satisfiability is co-r.e.-hard; the linked page gives undecidability, and a good expansion adds the co-r.e.-completeness of the tiling problem.

*Part 2.* For a Turing machine $T$, a formula $\varphi_T$ of AAULC is built whose models contain a grid representing the run of $T$, with a proposition $s_{\mathit{end}}$ marking halting; then $\varphi_T \to C\neg s_{\mathit{end}}$ is valid iff $T$ does not halt, and $\varphi_T \to \neg C\neg s_{\mathit{end}}$ is valid iff $T$ halts (Theorem 1 of the conference paper). Thus the halting problem and its complement both reduce to validity, and validity is not co-r.e. because the halting problem is not co-recognizable (Corollary 1).

## Sources

- H. van Ditmarsch, W. van der Hoek and L. B. Kuijer, "The undecidability of arbitrary arrow update logic", *Theoretical Computer Science* 693:1–12, 2017, <https://doi.org/10.1016/j.tcs.2017.07.018>; read as arXiv:1609.05686v1, <https://arxiv.org/abs/1609.05686v1>: Section 2 (the assumption on the number of agents), Section 3 (the tiling problem and the reduction, Theorem 1) and the concluding section.
- L. B. Kuijer, "Arbitrary arrow update logic with common knowledge is neither RE nor co-RE", in *Proceedings of the Conference on Theoretical Aspects of Rationality and Knowledge (TARK 2017)*, Electronic Proceedings in Theoretical Computer Science 251, 2017, pp. 373–381, <https://doi.org/10.4204/EPTCS.251.27>; read as arXiv:1707.08754v1, <https://arxiv.org/abs/1707.08754v1>: Section 2 (the assumption on the number of agents), Section 4 (Theorem 1, Corollaries 1 and 2) and Section 5.
