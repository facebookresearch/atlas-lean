# Propositional reachability for database-manipulating systems is undecidable

Whether a database-manipulating system can ever make a given proposition true is undecidable, already when the schema has a binary relation and guards are unions of conjunctive queries, or when it has just two unary relations and guards are first-order.

**Theorem.** The propositional reachability problem for [database-manipulating systems](database-manipulating-systems.md) is undecidable. It remains undecidable for each of the following restricted classes of inputs:

1. DMSs whose schema contains a binary relation, even when all guards are unions of conjunctive queries (the construction uses one binary and three unary relations besides propositions);
2. DMSs whose schema consists of two unary relations besides propositions, with first-order guards.

Both cases reduce from control-state reachability of two-counter Minsky machines (Appendix D of the source). Consequently, model checking DMSs against the source's monadic second-order specification language is undecidable.

## Depends on

- [Database-manipulating systems](database-manipulating-systems.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

Both cases reduce from control-state reachability of two-counter Minsky machines: given a machine with increment, guarded decrement and zero-test instructions, started in its initial state with both counters zero, can it reach a given control state? Control states are propositions of the DMS. With a binary relation $\mathit{Succ}$, both counters are chains of fresh values that start at a common element marked by a unary relation $\mathit{Zero}$, with unary relations $\mathit{Top}_1$, $\mathit{Top}_2$ marking their current ends; increment adds a $\mathit{Succ}$-edge to a fresh value and moves $\mathit{Top}_i$ there, decrement deletes the last edge and moves $\mathit{Top}_i$ back, and the zero test is the conjunctive query $\mathit{Top}_i(u) \land \mathit{Zero}(u)$. With two unary relations, counter $i$ is the number of elements in the $i$-th unary relation; increment adds a fresh value, decrement deletes one, and the zero test needs negation, hence first-order guards. Reaching the target proposition then corresponds exactly to the counter machine reaching its target state. Since the complement of propositional reachability is expressible as a model-checking query, model checking is undecidable too.

## Sources

- Parosh Aziz Abdulla, C. Aiswarya, Mohamed Faouzi Atig, Marco Montali and Othmane Rezine, "Recency-Bounded Verification of Dynamic Database-Driven Systems", in *Proceedings of the 35th ACM SIGMOD-SIGACT-SIGAI Symposium on Principles of Database Systems (PODS 2016)*, ACM, 2016, pp. 195–210, <https://doi.org/10.1145/2902251.2902300>; read as the extended version arXiv:1604.03413v1, <https://arxiv.org/abs/1604.03413v1>: Theorem 4.1 (Section 4) and Appendix D ("Undecidability of Propositional Reachability"), in the numbering of that version.
