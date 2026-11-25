# Positive relational algebra = unions of conjunctive queries = positive existential calculus

Over a fixed schema and constant set, the following query languages define the same queries: the SPJRU algebra
(selection with equality conditions, projection, natural join, renaming, union and constant singleton relations;
no difference), rule-based conjunctive queries with union (sets of rules with the same head relation, equality atoms
allowed) and the positive existential calculus, that is, the domain-independent calculus queries whose only
connectives are $\wedge$, $\vee$ and $\exists$. Without union, the satisfiable SPJR queries are exactly the
rule-based conjunctive queries. Each qualification matters: $\sigma_{A=a}(\sigma_{A=b}(R))$ with $a \ne b$ is an SPJR
query that is always empty, while every conjunctive query without equality atoms is satisfiable; unions of tableau
queries with one shared summary row are strictly weaker than SPJRU; and a positive existential formula with a free
variable not bound by a relation atom need not be domain independent, so need not define a relational query
(Abiteboul, Hull and Vianu, Theorems 4.4.8, 4.5.2 and 5.4.10).

## Expansion

This node states a precise result.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Conjunctive queries, answers and canonical databases.

## Depends on

- [Relational algebra queries](../relational-algebra/expr.md)
- [Relational calculus and domain independence](relational-calculus-and-domain-independence.md)
- [Named and positional relational carriers](named-positional-relational-carrier-bridge.md)

## Sources

- Foundations of Databases (Abiteboul, Hull, Vianu) — Abiteboul, Hull, Vianu; authors' free web edition (webdam.inria.fr/Alice), Theorem 4.4.8 (p. 60), Theorem 4.5.2 and the union-of-tableaux remark after it (p. 63), and Theorem 5.4.10 with the definition of positive existential queries before it (p. 91), all.pdf. <http://webdam.inria.fr/Alice/pdfs/all.pdf>
