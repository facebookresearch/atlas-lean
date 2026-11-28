# Regular path query entailment under finite-unification-set rulesets is undecidable

Although conjunctive queries are first-order rewritable under finite-unification-set rulesets, entailment of Boolean regular path queries under such rulesets is undecidable. For sticky rulesets it becomes decidable, but allowing higher-arity predicates in the paths makes it undecidable again.

**Theorem (Ostropolski-Nalewaja and Rudolph).** The following problems are undecidable:

1. given a database $D$, a fus ruleset $\mathcal{R}$ and a Boolean regular path query $Q$, is $Q$ entailed by $(D, \mathcal{R})$?
2. given a database $D$, a sticky ruleset $\mathcal{R}$ and a Boolean higher-arity regular path query $Q$, is $Q$ entailed by $(D, \mathcal{R})$?

Rules have single-atom heads, but the authors note that their results transfer to multi-head rules. Entailment of Boolean RPQs (with binary predicates only) under sticky rulesets is decidable, the paper's main positive result. In part 1 the ruleset of the reduction is the union of a sticky ruleset and a ruleset whose chase stops after a fixed number of steps; the undecidability also survives a single non-recursive projection step appended to a sticky ruleset.

## Depends on

- [Regular path query entailment under existential rules](regular-path-queries-under-existential-rules.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)
- [Halting is undecidable](../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

The reduction is from halting of two-counter automata. The ruleset builds an infinite grid whose points carry their coordinates, with edges for incrementing and decrementing either coordinate and for zero tests; the query's regular language describes the instruction sequence of an accepting run, so that the chase of the constructed database satisfies the query exactly when the automaton halts from $(0, 0)$ in its initial state (Lemma 10 of the arXiv version). For part 2 the last rules are changed so that the increment, decrement and zero-test predicates carry the coordinates as extra arguments, which makes the ruleset sticky; projecting these predicates to their first two positions recovers the earlier construction.

A good expansion links pages for the grid-building fus ruleset and for Lemma 10, which ties the query on its chase to halting of the two-counter automaton.

## Sources

- Piotr Ostropolski-Nalewaja and Sebastian Rudolph, "The Sticky Path to Expressive Querying: Decidability of Navigational Queries under Existential Rules", Proceedings of the 21st International Conference on Principles of Knowledge Representation and Reasoning (KR 2024), pp. 574–584, 2024, <https://doi.org/10.24963/kr.2024/54>; Theorem 7 (part 1) with Definition 8 and Lemma 10 in Section 3, Theorem 12 (sticky rulesets), and Theorem 38 (part 2) with the discussion in Section 5 of arXiv:2407.14384v1 (the copy read), <https://arxiv.org/abs/2407.14384v1>.
