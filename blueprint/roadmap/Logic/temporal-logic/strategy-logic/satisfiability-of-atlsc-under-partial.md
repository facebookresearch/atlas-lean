# Satisfiability of ATLsc under partial observation is undecidable

With partial observation, satisfiability of ATL with strategy contexts is undecidable even over turn-based game structures, although under full observation turn-based satisfiability is decidable.

**Theorem (Laroussinie, Markey and Sangnier).** A *concurrent game structure with partial observation* (CGSO) is a finite-state concurrent game structure together with an equivalence relation $\sim_a$ on states for each agent $a$; histories of equal length are $a$-equivalent if they are pointwise $\sim_a$-equivalent, and strategies of $a$ must give the same move after $a$-equivalent histories. It is *turn-based* (a TBGSO) if each state has an owner whose move alone determines the successor. Interpret [$\mathrm{ATL}^*_{sc}$, $\mathrm{ATL}_{sc}$, $\mathrm{ATL}^*_{sc,0}$ and $\mathrm{ATL}_{sc,0}$](atl-with-strategy-contexts.md) over CGSOs with strategy quantifiers ranging over such observation-respecting strategies (memoryless ones in the two variants with subscript $0$). For each of these four logics, the problem of deciding, given a formula $\Phi$, whether there exist a CGSO, an observation relation and a state satisfying $\Phi$ is undecidable, even when restricted to turn-based structures. This is Theorem 16 of the source, which reuses the reduction of Troquard and Walther from modal-logic satisfiability to $\mathrm{ATL}_{sc}$ satisfiability.

Partial observation changes satisfiability: the formula $\mathbf{AX}(\langle{\cdot} a_1 {\cdot}\rangle\mathbf X f) \wedge \neg\langle{\cdot} a_1 {\cdot}\rangle\mathbf{X}\mathbf X f$ is satisfiable with partial observation but not with full observation. Model checking $\mathrm{ATL}^*_{sc}$ over CGSOs with uniform observation (all agents sharing one equivalence) is decidable (Corollary 11 of the source).

## Depends on

- [ATL with strategy contexts](atl-with-strategy-contexts.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof reuses the reduction of Troquard and Walther, which translates formulas $\Phi$ of a multimodal logic written $\mathrm{S5}_n$ there into ATLsc formulas $\langle{\cdot}\emptyset{\cdot}\rangle\widehat\Phi$ satisfiable iff $\Phi$ is. The formulas $\widehat\Phi$ use only Boolean operators, strategy quantifiers $\langle{\cdot} a_i {\cdot}\rangle$ and formulas $\mathbf X P$, without $\mathbf U$ or nested $\mathbf X$; hence every strategy quantifier is evaluated at a single state and only the moves at that state matter, so adding observation relations or restricting to memoryless strategies does not change their meaning. A satisfying concurrent structure is converted into a turn-based one with partial observation (Theorem 6 of the source), and conversely a model with partial observation yields an $\mathrm{S5}_n$ model as in the full-observation case.

## Sources

- F. Laroussinie, N. Markey and A. Sangnier, "ATLsc with partial observation", in *Proceedings of the Sixth International Symposium on Games, Automata, Logics and Formal Verification (GandALF 2015)*, Electronic Proceedings in Theoretical Computer Science 193, 2015, pp. 43–57, <https://doi.org/10.4204/EPTCS.193.4>; numbers from arXiv:1509.07208v1, <https://arxiv.org/abs/1509.07208v1>: Definitions 1 and 2, Theorem 6, Corollary 11 and Theorem 16 with its proof (Section 5).
- N. Troquard and D. Walther, "On satisfiability in ATL with strategy contexts", in *Logics in Artificial Intelligence (JELIA 2012)*, Lecture Notes in Computer Science 7519, Springer, 2012, pp. 398–410, <https://doi.org/10.1007/978-3-642-33353-8_31>: the reduction reused in the proof; not read directly here: this clause rests on its statement in the arXiv copy of the first source above (proof of Theorem 16).
