# Every conjunctive query has a core, and every core is a minimization

Every conjunctive query $q$ has at least one [core](minimizations-and-cores-of-conjunctive-queries.md), and every core of $q$
is a minimization of $q$. The key step is: if $q_1(\bar y)$ is equivalent to a conjunctive query with fewer body atoms,
then some $q_3(\bar y)$ with $A_{q_3} \subsetneq A_{q_1}$ satisfies $(q_1, \bar y) \to (q_3, \bar y)$, namely the image of
the shorter query under a homomorphism into $q_1$.

## Depends on

- [Minimizations and cores of conjunctive queries](minimizations-and-cores-of-conjunctive-queries.md)

## Proof depends on

- [Homomorphism theorem for conjunctive queries with constants](homomorphism-theorem-for-conjunctive-queries-with-constants.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Proposition 16.4 and Lemma 16.5 (p. 126).
