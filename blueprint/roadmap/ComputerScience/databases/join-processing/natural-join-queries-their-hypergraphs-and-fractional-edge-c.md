# Natural join queries, their hypergraphs and fractional edge covers

For a full natural join $Q$, the pair $(\rho(Q),\rho^*(Q))$ gives the least size of an integral edge cover and the least total weight of a fractional edge cover. The input is a [relational expression](../relational-algebra/expr.md) and a schema assigning a finite heading $A_R$ to each relation name $R$. A base relation or a binary natural join of such expressions is a full join; any other operator, including projection, gives no pair.

Let $\sigma$ be the finite set of names occurring in $Q$. Its [named hypergraph](edge-covers/join-hypergraph-2.md) has vertex set $V=\bigcup_{R\in\sigma} A_R$, exactly the [output heading](edge-covers/schema-of-join-hypergraph.md), and one edge $A_R$ labelled by each $R\in\sigma$. Repeating a name does not introduce a second variable in the covering problem. Two **different** names with the same heading do give separate edges. A join expression has at least one leaf, but headings, and hence $V$, can be empty.

- $\rho(Q)$ is the [minimum cardinality](edge-covers/is-least-edge-cover-number.md) of a set $C\subseteq\sigma$ for which $\bigcup_{R\in C}A_R=V$.
- $\rho^*(Q)$ is the [minimum total weight](edge-covers/is-least-fractional-edge-cover-number.md) $\sum_{R\in\sigma}x_R$ over all real $x_R\geq0$ satisfying $\sum_{R\in\sigma:\,a\in A_R}x_R\geq1$ for every $a\in V$. Attributes outside $V$ impose no constraint.

The [triangle join](edge-covers/triangle-cover-numbers.md) has $(\rho,\rho^*)=(2,3/2)$. The weights here are on **relations**: these are the covers in the [AGM bound](agm-output-size-bound-for-join-queries.md), not the [fractional vertex covers](query-hypergraph-and-fractional-vertex-covering-number.md) used in the communication lower bound.

## Sources

- A. Atserias, M. Grohe and D. Marx, [*Size Bounds and Query Plans for Relational Joins*](http://www.cs.bme.hu/~dmarx/papers/atserias-sicomp2013-joins.pdf), SIAM J. Comput. 42(4) (2013), 1737–1767, §§1–2 and §3.1, LP (3.1). In the authors' revised manuscript dated 29 June 2013, pp. 2–3 give the triangle and its cover numbers, p. 5 defines the query schema and (multi-)hypergraph, and p. 6 gives LP (3.1).
