# Metatiles with at most two combs

Let $Q$ be a finite set of natural numbers and $q$ its
largest element ($q = 0$ for $Q = \emptyset$). The set $Q$ has metatiles with at most two combs
if for all natural numbers $N$ and $k$ and every restricted-overlap tiling of an $N$-board with
squares and $k$ $Q$-combs, with set $P$ of comb start cells, any three combs $a < b < c$ in $P$
are separated by a boundary: there is a natural number $j$ with $a < j \le c$ such that no comb
$s \in P$ satisfies $s < j \le s + q$.

A metatile is a gapless grouping of tiles that cannot be split into smaller gapless groupings.
The boundary before cell $j$ separates two metatiles exactly when no tile straddles it, that is,
when no comb $s \in P$ has $s < j \le s + q$ (squares never straddle a boundary). So the
condition says that every metatile of every such tiling contains at most two combs.

## Sources

- Michael A. Allen, *Connections Between Combinations Without Specified Separations and Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer Sequences 28 (2025), Article 25.3.7, Section 1 (metatiles) and Lemma 15.
