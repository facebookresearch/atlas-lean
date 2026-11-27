# Dead vertices have no escape

Suppose the partner array describes a matching. Run the
search at level $k$ from a right vertex $z$ first reached in round $k + 1$, with a set $U$ of used
left vertices and an initial set $D$ of dead right vertices, and let $D'$ be the dead set after
it. Then every right vertex $y$ in $D'$ but not in $D$ has no escape avoiding $U$ and $D'$: if $y$
is first reached in round $m + 1$, no alternating chain from $y$ to an unmatched left vertex with
$m + 1$ pairs has all its left vertices outside $U$ and all its right vertices after $y$ outside
$D'$.

So Hopcroft and Karp's pruning loses no path.
