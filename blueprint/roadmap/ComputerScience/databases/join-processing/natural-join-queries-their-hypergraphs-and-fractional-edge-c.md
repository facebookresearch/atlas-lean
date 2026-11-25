# Natural join queries, their hypergraphs and fractional edge covers

A full natural join query $Q = R_1(\mathbf{A}_1) \bowtie \dots \bowtie R_m(\mathbf{A}_m)$ has the hypergraph
$H(Q)$ whose vertices are the attributes and whose hyperedges are the attribute sets $\mathbf{A}_j$. An edge
cover is a set of hyperedges containing every attribute, and $\rho(Q)$ is the least size of one. A fractional
edge cover is $x \in \mathbb{R}^m_{\ge 0}$ with $\sum_{j : v \in \mathbf{A}_j} x_j \ge 1$ for every attribute $v$, and
$\rho^*(Q)$ is the least value of $\sum_j x_j$. This is the covering problem of the [AGM bound](agm-output-size-bound-for-join-queries.md); it is not the
fractional vertex cover of the MPC lower bound. For example, the triangle query has $\rho = 2$ and
$\rho^* = 3/2$.

## Depends on

- [Relational algebra queries](../relational-algebra/expr.md)

## Sources

- Size Bounds and Query Plans for Relational Joins (Atserias, Grohe, Marx), SIAM J. Comput. 42(4) 2013 — SIAM Journal on Computing, Section 1, fractional covers paragraph (p.1739), and Section 3.1, linear program (3.1) (p.1742). <http://www.cs.bme.hu/~dmarx/papers/atserias-sicomp2013-joins.pdf>
