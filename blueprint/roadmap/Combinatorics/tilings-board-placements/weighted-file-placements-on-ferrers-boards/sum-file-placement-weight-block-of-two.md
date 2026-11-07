# Weights cancel on a block with two rooks in the chosen level

Let $m \ge 2$, let $B$ be a
singleton board for $m$, with rows numbered from $0$ and row $r$ in level $\lfloor r/m \rfloor$,
and let $F_0$ be a file placement on $B$. Let $l$ be the chosen level of $F_0$ (among the levels
holding at least two cells of $F_0$, one holding the fewest, the lowest on ties) and $c_0$ the
leftmost cell of $F_0$ in level $l$, and suppose that level $l$ holds exactly two cells of $F_0$.
Then the $m$-weights $\operatorname{wt}_m(F)$ of the file placements $F$ in the block $P(F_0)$
sum to $0$, where $P(F_0)$ consists of the file placements on $B$ that agree with $F_0$ outside
level $l$, use the same columns as $F_0$ inside level $l$, and contain $c_0$.

## Sources

- Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024), Article A58, Lemma 8 (`integers-2024-A58-lem-8`).
