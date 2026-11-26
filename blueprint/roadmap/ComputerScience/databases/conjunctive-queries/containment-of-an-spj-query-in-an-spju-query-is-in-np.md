# Containment of an SPJ query in an SPJU query is in NP

An SPJ query is a relational algebra expression built from relation names with selection by equality conditions,
projection, product and renaming; an SPJU query may also use union. Every SPJU query $e$ is equivalent to the union of
the set $\mathrm{SPJ}(e)$ of SPJ queries obtained by resolving each union node of $e$ to one of its two arguments.
Deciding, for an SPJ query $e$ and an SPJU query $e'$, whether $e \subseteq e'$ (that is, $e(D) \subseteq e'(D)$ on
every database $D$) is in NP: guess a member $e''$ of $\mathrm{SPJ}(e')$ and a homomorphism from the conjunctive query
of $e''$ to that of $e$.

## Depends on

- [Relational algebra queries](../relational-algebra/expr.md)
- [The complexity class NP](../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/np.md)

## Proof depends on

- [Positive relational algebra = unions of conjunctive queries = positive existential calculus](../relational-calculus/positive-relational-algebra-unions-of-conjunctive-queries-po.md)
- [Chandra-Merlin containment criterion](../../not-yet-classified/conjunctive-queries/contained-iff-hom.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Proposition 29.4 (p. 255) and Proposition 29.5 (p. 256).
