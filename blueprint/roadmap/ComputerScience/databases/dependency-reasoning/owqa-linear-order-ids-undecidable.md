# Query answering over a linear order with inclusion dependencies is undecidable

When a distinguished relation must be a strict linear order, open-world query answering is undecidable for a fixed conjunctive query that is not base-covered and a fixed set of inclusion dependencies that do not mention the order, with the finite set of facts as input.

**Theorem.** There are a signature $\sigma = \sigma_B \sqcup \sigma_D$ in which $\sigma_D$ consists of a single distinguished relation $<$, required to be a strict linear order, a CQ $Q$ on $\sigma$ and a set $\Sigma$ of inclusion dependencies on $\sigma_B$ such that the following problem is undecidable: given a finite set of facts $F_0$, decide $\mathrm{QA}^{lin}(F_0, \Sigma, Q)$, that is, whether every set of facts $F \supseteq F_0$ satisfying $\Sigma$ in which $<$ is a strict linear order on the elements of $F$ satisfies $Q$. The notions are those of [Query answering with transitive relations, transitive closure and linear orders](query-answering-over-transitive-and-ordered-data.md).

Since $\Sigma$ does not mention the order, the constraints are base-covered; the query is not base-covered.

## Depends on

- [Syntax of an inclusion dependency](../dependencies-and-the-chase/ind.md)
- [Answers of a conjunctive query](../conjunctive-queries/answers-of-a-conjunctive-query.md)
- [Query answering with transitive relations, transitive closure and linear orders](query-answering-over-transitive-and-ordered-data.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

As for transitive closure, the proof reduces from an undecidable infinite tiling problem with fixed colors and fixed forbidden horizontal and vertical pairs, whose input prescribes the colors of an initial segment of one side of the quadrant. The signature has binary relations $R$ and $D$ (right and down), unary relations $K_1, \dots, K_{k-1}$ and a unary relation $S$ for grid vertices. The inclusion dependencies $S(x) \rightarrow \exists y\, R(x, y)$, $S(x) \rightarrow \exists y\, D(x, y)$, $R(x, y) \rightarrow S(y)$ and $D(x, y) \rightarrow S(y)$ generate right and down successors. The color of an element is coded by its position in the linear order relative to marker elements $b_1 < \dots < b_{k-1}$ with $K_j(b_j)$, so totality of the order gives every element a color. The query has disjuncts $R(x, y) \wedge D(x, z) \wedge R(z, w) \wedge D(y, w') \wedge w < w'$ and the same with $w' < w$, which force right-then-down and down-then-right to meet, and disjuncts detecting a forbidden horizontal or vertical pair of colors; the initial facts encode the first row and its prescribed colors. The source first proves the claim for a UCQ and then encodes it into a CQ. The result is close to an earlier undecidability result for UCQs with inequalities, whose inequalities a linear order can express.

A good expansion links the undecidability of this origin-constrained infinite tiling problem of the quadrant for a fixed tile system.

Taking $\Sigma' = \Sigma \wedge \neg Q$, which can be written as base frontier-guarded TGDs, the source derives that query answering over a linear order is undecidable for a fixed set of base frontier-guarded TGDs and the tautological query (Corollary 5). In contrast, it proves query answering over linear orders decidable in doubly exponential time for base-covered constraints of the base-covered guarded negation fragment and base-covered UCQs.

## Sources

- Antoine Amarilli, Michael Benedikt, Pierre Bourhis and Michael Vanden Boom, "Query answering with transitive and linear-ordered data", in *Proceedings of the 25th International Joint Conference on Artificial Intelligence (IJCAI 2016)*, pp. 893–898, 2016; extended journal version in *Journal of Artificial Intelligence Research* 63, pp. 191–264, 2018, doi:[10.1613/jair.1.11240](https://doi.org/10.1613/jair.1.11240); read in arXiv:1607.00813v1 ([arXiv](https://arxiv.org/abs/1607.00813v1)), the conference article with its appendix, whose numbering is used: Theorem 10 and Corollary 5 (Section 6), with the proof in the appendix ("Undecidability results related to linear orders").
