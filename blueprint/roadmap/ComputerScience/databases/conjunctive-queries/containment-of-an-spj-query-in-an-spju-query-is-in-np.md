# Containment of an SPJ query in an SPJU query is in NP

An SPJ query is a relational algebra expression built from relation names with selection by equality conditions,
projection, product and renaming; an SPJU query may also use union. Every SPJU query $e$ is equivalent to the union of
the set $\mathrm{SPJ}(e)$ of SPJ queries obtained by resolving each union node of $e$ to one of its two arguments.
Deciding, for an SPJ query $e$ and an SPJU query $e'$, whether $e \subseteq e'$ (that is, $e(D) \subseteq e'(D)$ on
every database $D$) is in NP. An SPJ query whose selections force two
distinct constants to be equal is empty on every database: if $e$ is such a query, $e \subseteq e'$ holds, and such
members of $\mathrm{SPJ}(e')$ can be discarded. Otherwise an SPJ query corresponds to a tableau query, a set of atoms with an output tuple (summary row) that may
contain constants, because a selection $\sigma_{A = c}$ fixes its output column to $c$; this is wider than the
conjunctive-query syntax, whose head holds only variables. Then
$e \subseteq e'$ if and only if some remaining member $e''$ of $\mathrm{SPJ}(e')$ has a homomorphism from its tableau to
that of $e$ that is the identity on constants and maps output tuple to output tuple; guess $e''$ and the homomorphism.

## Depends on

- [Relational algebra queries](../relational-algebra/expr.md)
- [The complexity class NP](../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/np.md)

## Proof depends on

- [Positive relational algebra = unions of conjunctive queries = positive existential calculus](../relational-calculus/positive-relational-algebra-unions-of-conjunctive-queries-po.md)
- [Chandra-Merlin containment criterion](../conjunctive-queries-and-the-chandra-merlin-theor/contained-iff-hom.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Proposition 29.4 (p. 263) and Proposition 29.5 (p. 264).
