# Tree criterion for fast wins

Let $S$ be a finite set of natural numbers and $p$ a
natural number. Let $T$ be a finite rooted tree with root $r$ whose vertices are pairwise
distinct rationals, such that every path from $r$ down to a vertex has at most $p$ vertices and
some such path has exactly $p$ vertices (so $T$ has height $p - 1$). Suppose that for every leaf
$v$ the set of vertices on the path from $r$ to $v$ contains a copy $aS + b$ of $S$ with
rationals $a > 0$ and $b$, and that every vertex other than the root that is not a leaf has at
least two children. Then, starting from the position where no number has been claimed, Maker
wins the $S$-game within $p$ moves.

The tree is given by the finite set of its root-to-vertex paths, each recorded as the list of
rationals along it.

## Sources

- Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40, Proposition 1.
