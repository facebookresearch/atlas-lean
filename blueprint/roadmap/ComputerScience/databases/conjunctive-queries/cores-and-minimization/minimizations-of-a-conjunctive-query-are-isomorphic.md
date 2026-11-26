# Minimizations of a conjunctive query are isomorphic

Any two minimizations of a conjunctive query $q$ are isomorphic. Consequently any two
[cores](minimizations-and-cores-of-conjunctive-queries.md) of $q$ are isomorphic, so the core of $q$ is unique up to
renaming of variables. In the proof, homomorphisms in both directions between two minimizations are bijections on
variables, since a non-surjective or non-injective one would yield an equivalent query with fewer atoms.

## Depends on

- [Minimizations and cores of conjunctive queries](minimizations-and-cores-of-conjunctive-queries.md)

## Proof depends on

- [Homomorphism theorem for conjunctive queries with constants](homomorphism-theorem-for-conjunctive-queries-with-constants.md)
- [Every conjunctive query has a core, and every core is a minimization](every-conjunctive-query-has-a-core-and-cores-are-minimizations.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Proposition 16.7, Lemma 16.8 and Corollary 16.9 (pp. 128–129).
- S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995; authors' web edition <http://webdam.inria.fr/Alice/pdfs/all.pdf>, Proposition 6.2.9 (p. 120).
