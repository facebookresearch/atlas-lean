# Finite determinacy of conjunctive queries is undecidable

No algorithm decides, given a finite set of conjunctive queries (the views) and a further conjunctive query, whether the views finitely determine the query, that is, whether any two finite databases with the same view answers give the same answer to the query.

**Theorem (Gogacz and Marcinkowski).** The conjunctive query finite determinacy problem is undecidable: there is no algorithm that, given a finite set $\mathcal{Q} = \{Q_1, \dots, Q_k\}$ of conjunctive queries and a conjunctive query $Q_0$ over a common relational schema (all part of the input), decides whether for all finite structures $\mathbb{D}_1, \mathbb{D}_2$ with $Q(\mathbb{D}_1) = Q(\mathbb{D}_2)$ for every $Q \in \mathcal{Q}$ one also has $Q_0(\mathbb{D}_1) = Q_0(\mathbb{D}_2)$.

The same authors proved earlier (LICS 2015) that the unrestricted version, with $\mathbb{D}_1, \mathbb{D}_2$ ranging over all structures, is undecidable; the two problems differ, since some $\mathcal{Q}$ finitely determines some $Q_0$ without determining it.

## Depends on

- [Determinacy of a query by views](determinacy-of-a-query-by-views.md)
- [Answers of a conjunctive query](../conjunctive-queries/answers-of-a-conjunctive-query.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Halting is undecidable](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

The proof first restates finite determinacy as a question about green–red tuple-generating dependencies: whether a set of "green graph rewriting rules" finitely leads to a fixed structure, the red spider. It then encodes a *rainworm machine*, a restricted rewriting device whose non-termination ("the rainworm creeps forever") is undecidable by a standard simulation of Turing machines (Lemma 21 in the numbering of arXiv:1512.01681v1, proved there by textbook techniques). Because rewriting rules are symmetric while machine instructions are not, the encoding first shows (Lemmas 22 and 23 of arXiv:1512.01681v1, subsection "Creeping back and forth") that when the rainworm halts, the configurations reachable from the initial one under the symmetric closure of its rewriting are exactly those that rewrite forward to the final configuration, which controls the extra moves the symmetric rules allow.

## Sources

- Tomasz Gogacz and Jerzy Marcinkowski, "Red Spider Meets a Rainworm: Conjunctive Query Finite Determinacy Is Undecidable", Proceedings of the 35th ACM SIGMOD-SIGACT-SIGAI Symposium on Principles of Database Systems (PODS 2016), pp. 121–134, 2016, <https://doi.org/10.1145/2902251.2902288>; Theorem 1 (main result) and Theorem 5 (equivalent form CQfDP.3) in the numbering of arXiv:1512.01681v1, <https://arxiv.org/abs/1512.01681v1>.
- Tomasz Gogacz and Jerzy Marcinkowski, "The Hunt for a Red Spider: Conjunctive Query Determinacy Is Undecidable", 30th Annual ACM/IEEE Symposium on Logic in Computer Science (LICS 2015), pp. 281–292, 2015, <https://doi.org/10.1109/LICS.2015.35>; undecidability of unrestricted determinacy (prose), Theorem 1 of arXiv:1501.01817v2 (the copy read), <https://arxiv.org/abs/1501.01817v2>.
