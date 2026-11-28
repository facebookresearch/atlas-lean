# Finite conjunctive query entailment over ALC with role cover axioms is undecidable

Whether every finite model of an $\mathcal{ALC}$ TBox extended with role cover axioms satisfies a given Boolean conjunctive query is undecidable; consequently conjunctive query entailment for $\mathcal{ALCSCC}^{++}$ is undecidable.

**Role cover axioms.** $\mathcal{ALC}^{\mathrm{cov}}$ extends $\mathcal{ALC}$ TBoxes by axioms $\mathrm{cov}(r,s)$ for role names $r, s$; an interpretation $\mathcal{I}$ satisfies $\mathrm{cov}(r,s)$ iff $r^{\mathcal{I}} \cup s^{\mathcal{I}} = \Delta^{\mathcal{I}} \times \Delta^{\mathcal{I}}$.

**Theorem (Baader, Bednarczyk and Rudolph).**

1. Finite conjunctive query entailment over $\mathcal{ALC}^{\mathrm{cov}}$ TBoxes is undecidable: there is no algorithm that decides, for an $\mathcal{ALC}^{\mathrm{cov}}$ TBox $\mathcal{T}$ and a Boolean conjunctive query $q$, whether every finite model of $\mathcal{T}$ satisfies $q$ (Theorem 25).
2. Conjunctive query entailment for [$\mathcal{ALCSCC}^{++}$](description-logics-with-cardinality-constraints/alcscc-with-global-and-local-cardinality.md) is undecidable (Corollary 26).

Clause 1 gives a very restricted fragment of constant-free, equality-free two-variable first-order logic, extended by conjunctive queries, in which finite query entailment is undecidable. In contrast, conjunctive query entailment for $\mathcal{ALCSCC}$ ABoxes with respect to $\mathcal{ALCSCC}$ ERCBoxes is decidable (Section 7).

## Depends on

- [ALC syntax, semantics and reasoning tasks](../alc-syntax-semantics-and-reasoning-tasks.md)
- [The description logic ALCSCC++ with global and local cardinality constraints](description-logics-with-cardinality-constraints/alcscc-with-global-and-local-cardinality.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Halting is undecidable](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

The reduction is from the looping problem for deterministic Turing machines started on the empty tape (whether the run never halts). For a machine $\mathcal{M}$ one builds an $\mathcal{ALC}^{\mathrm{cov}}$ TBox $\mathcal{T}$ and a CQ $Q$ such that $\mathcal{M}$ loops iff some finite model of $\mathcal{T}$ does not satisfy $Q$ (Proposition 24); the TBox and query use only two variables, no constants and no equality. Clause 2 follows because $\mathcal{ALCSCC}^{++}$ subsumes $\mathcal{ALC}^{\mathrm{cov}}$ and has only finite interpretations, so its entailment is finite entailment.

## Sources

- Franz Baader, Bartosz Bednarczyk and Sebastian Rudolph, "Satisfiability and query answering in description logics with global and local cardinality constraints", in *ECAI 2020: 24th European Conference on Artificial Intelligence*, Frontiers in Artificial Intelligence and Applications 325, IOS Press, 2020, doi:10.3233/FAIA200146; read as arXiv:2002.06072v1, <https://arxiv.org/abs/2002.06072v1>: Theorem 25, Corollary 26, Proposition 24 and Sections 6 and 7 of arXiv:2002.06072v1.
