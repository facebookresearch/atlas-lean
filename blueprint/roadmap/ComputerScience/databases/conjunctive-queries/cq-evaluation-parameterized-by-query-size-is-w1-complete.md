# Conjunctive-query evaluation parameterized by query size is W[1]-complete

p-CQ-Evaluation is the parameterized problem whose input is a conjunctive query $q(\bar x)$, a database $D$ and a tuple
$\bar a$ over $\mathrm{Dom}(D)$, whose question is whether $\bar a \in q(D)$, and whose parameter is the size
$\lVert q \rVert$ of the encoding of $q$. Take $\mathrm{W}[1]$ to be the class of parameterized problems that
FPT-reduce to the weighted definability problem of some universal first-order sentence $\varphi$ over a schema
extended by a relation name $X$ (given a database $D$ and the parameter $k \in \mathbb N$, is there a set $S$ of $k$ tuples from
$\mathrm{Dom}(D)^{\mathrm{ar}(X)}$ with $D \models \varphi(S)$, interpreting $X$ by $S$). Then p-CQ-Evaluation is $\mathrm{W}[1]$-complete under
FPT-reductions: it lies in $\mathrm{W}[1]$, and every parameterized problem in $\mathrm{W}[1]$ FPT-reduces to it. Hardness holds already for
Boolean queries, by the reduction from $k$-Clique that maps a graph $G = (V, E)$ and $k \ge 1$ to the database
$\{\mathrm{Node}(v) : v \in V\} \cup \{\mathrm{Edge}(u, v) : \{u, v\} \in E, u \ne v\}$ and the query
$\exists x_1 \cdots \exists x_k \bigwedge_i \mathrm{Node}(x_i) \wedge \bigwedge_{i \ne j} \mathrm{Edge}(x_i, x_j)$.

## Depends on

- [Answers of a conjunctive query](answers-of-a-conjunctive-query.md)
- [Parameterized problems](../../../TheoryOfComputation/complexity-classes/parameterized-complexity/param-problem.md)
- [FPT-reductions](../../../TheoryOfComputation/complexity-classes/parameterized-complexity/fptreduces.md)

## Proof depends on

- [Parameterized complexity: FPT and W(1)-completeness of Clique](../../../TheoryOfComputation/complexity-classes/parameterized-complexity/parameterized-clique-w1-complete.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, the problem p-CQ-Evaluation (p. 112), the problem p-WD and Definition 14.6 (pp. 113–114), and Theorem 14.7 (p. 115).
