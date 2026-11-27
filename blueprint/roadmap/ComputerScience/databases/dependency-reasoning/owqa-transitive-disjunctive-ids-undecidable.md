# Query answering over transitive relations with disjunctive inclusion dependencies is undecidable

When a distinguished binary relation is only required to be transitive, open-world query answering is undecidable for a fixed set of disjunctive inclusion dependencies, which are not base-guarded, and a fixed conjunctive query, over a signature of arity two, with the finite set of facts as input.

**Theorem.** There are a signature $\sigma = \sigma_B \sqcup \sigma_D$ whose relations have arity at most two and in which $\sigma_D$ consists of a single distinguished relation $S^+$, required to be transitive, a set $\Sigma$ of [disjunctive inclusion dependencies](disjunctive-inclusion-dependencies.md) on $\sigma$ and a CQ $Q$ on $\sigma_B$ such that the following problem is undecidable: given a finite set of facts $F_0$, decide $\mathrm{QA}^{tr}(F_0, \Sigma, Q)$, that is, whether every set of facts $F \supseteq F_0$ satisfying $\Sigma$ in which $S^+$ is transitive satisfies $Q$. The notions are those of [Query answering with transitive relations, transitive closure and linear orders](query-answering-over-transitive-and-ordered-data.md).

## Depends on

- [Disjunctive inclusion dependencies](disjunctive-inclusion-dependencies.md)
- [Answers of a conjunctive query](../conjunctive-queries/answers-of-a-conjunctive-query.md)
- [Query answering with transitive relations, transitive closure and linear orders](query-answering-over-transitive-and-ordered-data.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof reduces from an undecidable infinite tiling problem with fixed colors $C_1, \dots, C_k$ and fixed forbidden horizontal and vertical pairs, whose input prescribes the colors $c_0, \dots, c_n$ of the first column. The signature has a binary successor relation $S'$, the transitive relation $S^+$, a binary relation $K_i$ and a unary relation $K'_i$ for each color, and the constraints are

$$
S'(x, y) \rightarrow \exists z\, S'(y, z), \qquad S'(x, y) \rightarrow S^+(x, y),
$$

$$
S^+(x, y) \rightarrow \bigvee_i K_i(x, y), \qquad S^+(x, y) \rightarrow \bigvee_i K_i(y, x), \qquad S^+(x, y) \rightarrow \bigvee_i K'_i(x),
$$

where $K_i(x, y)$ says that the cell indexed by the pair of positions $(x, y)$ has color $C_i$, and $K'_i(x)$ plays the role of $K_i(x, x)$ for the diagonal cells (a separate predicate, since variables cannot repeat in an inclusion dependency). By transitivity every ordered pair of positions of the generated chain gets a color in both orders. The initial facts encode a chain $a_0, \dots, a_n$ of $S'$-facts and the prescribed colors $K_j(a_0, a_i)$ and $K'_j(a_0)$, and the query detects a forbidden horizontal or vertical pair of adjacent cells; the source proves the result first for a UCQ and then adapts it to a CQ. The tiling problem has a solution exactly when some superset of $F_0$ satisfies $\Sigma$, violates $Q$ and has $S^+$ transitive.

A good expansion links the undecidability of this origin-constrained infinite tiling problem of the quadrant for a fixed tile system.

In contrast, the same source proves query answering over transitive relations decidable for base frontier-guarded TGDs and UCQs, and cites earlier work showing undecidability on arity-two signatures for guarded TGDs and atomic queries even when transitive relations occur only in guards.

## Sources

- Antoine Amarilli, Michael Benedikt, Pierre Bourhis and Michael Vanden Boom, "Query answering with transitive and linear-ordered data", in *Proceedings of the 25th International Joint Conference on Artificial Intelligence (IJCAI 2016)*, pp. 893–898, 2016; extended journal version in *Journal of Artificial Intelligence Research* 63, pp. 191–264, 2018, doi:[10.1613/jair.1.11240](https://doi.org/10.1613/jair.1.11240); read in arXiv:1607.00813v1 ([arXiv](https://arxiv.org/abs/1607.00813v1)), the conference article with its appendix, whose numbering is used: Theorem 9 (Section 5), with its proof in the appendix ("Undecidability results related to transitivity").
