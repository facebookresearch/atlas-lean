# Every union of conjunctive queries has a core, and every core is a minimization

Every union of conjunctive queries $q$ has at least one [core](minimizations-and-cores-of-unions-of-conjunctive-queries.md),
and every core of $q$ is a minimization of $q$. A core is obtained by replacing each disjunct by one of its cores and then
removing, while possible, a disjunct contained in another remaining disjunct; whatever the choices, the result is a core.

## Depends on

- [Minimizations and cores of unions of conjunctive queries](minimizations-and-cores-of-unions-of-conjunctive-queries.md)

## Proof depends on

- [Every conjunctive query has a core, and every core is a minimization](every-conjunctive-query-has-a-core-and-cores-are-minimizations.md)
- [Removing redundant atoms computes a core](removing-redundant-atoms-computes-a-core.md)
- [Containment of unions of conjunctive queries](containment-of-unions-of-conjunctive-queries.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Proposition 29.10, Algorithm 16 (ComputeCoreUCQ) and Lemma 29.11 (pp. 266–267).
