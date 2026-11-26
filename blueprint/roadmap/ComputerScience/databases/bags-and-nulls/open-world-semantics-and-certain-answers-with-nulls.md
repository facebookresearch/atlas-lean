# Open-world semantics and certain answers with nulls

Fix a countably infinite set $\mathrm{Const}$ of constants and a disjoint countably infinite set $\mathrm{Null}$ of
nulls. An incomplete instance $I$ is a finite set of facts whose entries are constants or nulls; a valuation $h$ maps
each null of $I$ to a constant and fixes constants. Under the closed-world assumption $I$ represents
$[\![I]\!]_{\mathrm{cwa}} = \{h(I) : h \text{ a valuation}\}$, and under the open-world assumption
$[\![I]\!]_{\mathrm{owa}} = \{D : h(I) \subseteq D \text{ for some valuation } h\}$. The answers $q(D)$ of a query on a
database are computed with the answer variables ranging over the elements of $D$ and the constants of $q$. For a query
$q$, a tuple $\bar a$ over $\mathrm{Dom}(I) \cup \mathrm{Const}(q)$ is a certain answer, written
$\bar a \in \mathrm{cert}_{\mathrm{cwa}}(q, I)$, if $h(\bar a) \in q(h(I))$ for every valuation $h$, and
$\bar a \in \mathrm{cert}_{\mathrm{owa}}(q, I)$ if $h(\bar a) \in q(D)$ for every valuation $h$ and every database $D$
with $h(I) \subseteq D$. For tuples without nulls this is membership in the intersection of $q(D)$ over the represented
databases $D$, and if $I$ has no nulls then $\mathrm{cert}_{\mathrm{cwa}}(q, I) = q(I)$. The two semantics differ: for
the query "every person has a recorded profession", a closed-world certain answer can be true while the open-world one
is false.

## Depends on

- [Incomplete databases, possible worlds and certain answers](incomplete-databases-possible-worlds-and-certain-answers.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Definitions 39.1 and 39.2 (pp. 368–369), with the constants and nulls of Chapter 39, Definition 39.3, Proposition 39.4 and Example 39.5 (pp. 370–371).
