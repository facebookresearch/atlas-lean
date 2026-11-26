# Generalized hypertreewidth at most one is acyclicity

A conjunctive query has generalized hypertreewidth at most $1$ if and only if it is acyclic, that is, its hypergraph $H_q$
(variables as vertices, the variable sets of the atoms as hyperedges) has a join tree: a tree on the hyperedges in
which, for every variable, the hyperedges containing it form a connected subtree. So $\mathrm{GHW}(1)$ is the class
of acyclic conjunctive queries. A query whose atoms have no variables, such as $\mathrm{Answer}() \mathrel{:-} R(a)$, has
width $0$.

## Depends on

- [Generalized hypertree decompositions and generalized hypertreewidth](generalized-hypertree-decompositions-and-width.md)
- [Characterizations of acyclic database schemas](../join-processing/characterizations-of-acyclic-database-schemas.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Definitions 18.2 and 18.4 (pp. 152–154) and Proposition 22.3 (p. 185).
