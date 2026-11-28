# Query answering over transitive closure with inclusion dependencies is undecidable

When a distinguished relation must be the transitive closure of a base relation, open-world query answering becomes undecidable already for a fixed set of inclusion dependencies and a fixed conjunctive query over the base relations, with only the finite set of facts as input.

**Theorem.** There are a signature $\sigma = \sigma_B \sqcup \sigma_D$ in which $\sigma_D$ consists of a single distinguished binary relation $S^+$, interpreted as the transitive closure of a base relation $S$, a set $\Sigma$ of inclusion dependencies on $\sigma$ and a CQ $Q$ on $\sigma_B$ such that the following problem is undecidable: given a finite set of facts $F_0$, decide $\mathrm{QA}^{tc}(F_0, \Sigma, Q)$, that is, whether every set of facts $F \supseteq F_0$ satisfying $\Sigma$ in which $S^+$ is the transitive closure of $S$ satisfies $Q$. The notions are those of [Query answering with transitive relations, transitive closure and linear orders](query-answering-over-transitive-and-ordered-data.md).

Base inclusion dependencies, whose body atom is a base relation, would make the problem decidable, so some of these inclusion dependencies have the distinguished relation in their body.

## Depends on

- [Syntax of an inclusion dependency](../dependencies-and-the-chase/ind.md)
- [Answers of a conjunctive query](../conjunctive-queries/answers-of-a-conjunctive-query.md)
- [Query answering with transitive relations, transitive closure and linear orders](query-answering-over-transitive-and-ordered-data.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof reduces from an undecidable infinite tiling problem with a fixed set of colors $C_1, \dots, C_k$ and fixed sets of forbidden horizontal and vertical pairs, whose input is a sequence $c_0, \dots, c_n$ of colors prescribed on the first column: is there $f : \mathbb{N}^2 \to \{C_1, \dots, C_k\}$ with $f(0, i) = c_i$ for $i \le n$ and no forbidden pair between horizontally or vertically adjacent cells? The constraints use a transitive successor relation to generate a grid of pairs of integers, use transitive closure to emulate the disjunction needed to choose a color, as in the source's polynomial-time translation of query answering with disjunctive inclusion dependencies and UCQs into query answering over transitive closure with base inclusion dependencies and a base-covered CQ, and the query detects a forbidden adjacent pattern; the source first proves the result for a UCQ and then encodes it into a CQ. The tiling problem has a solution exactly when some superset of $F_0$ satisfies $\Sigma$, violates $Q$ and interprets $S^+$ as the transitive closure of $S$.

A good expansion links the undecidability of this origin-constrained infinite tiling problem of the quadrant for a fixed tile system, and the source's Theorem 5 (that translation of disjunctive inclusion dependencies into transitive closure).

In contrast, the same source proves query answering over transitive closure decidable for base frontier-guarded TGDs and UCQs, so the base-guardedness condition cannot be dropped.

## Sources

- Antoine Amarilli, Michael Benedikt, Pierre Bourhis and Michael Vanden Boom, "Query answering with transitive and linear-ordered data", in *Proceedings of the 25th International Joint Conference on Artificial Intelligence (IJCAI 2016)*, pp. 893–898, 2016; extended journal version in *Journal of Artificial Intelligence Research* 63, pp. 191–264, 2018, doi:[10.1613/jair.1.11240](https://doi.org/10.1613/jair.1.11240); read in arXiv:1607.00813v1 ([arXiv](https://arxiv.org/abs/1607.00813v1)), the conference article with its appendix, whose numbering is used: Theorem 8 (Section 5), with its proof in the appendix ("Undecidability results related to transitivity").
