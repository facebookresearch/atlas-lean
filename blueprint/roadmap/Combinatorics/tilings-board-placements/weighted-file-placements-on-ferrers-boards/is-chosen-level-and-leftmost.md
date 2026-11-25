# The chosen level and its leftmost cell

Let $m$ be a natural number and $F_0$ a finite set
of cells $(i, r)$ (column $i$, row $r$), and call the rows $r$ with $\lfloor r/m \rfloor = l$
level $l$ (for $m = 0$, every row lies in level $0$). A level $l$ and a cell $c_0$ are chosen for
$F_0$ when level $l$ contains at least two cells of $F_0$; every level $l'$ containing at least
two cells of $F_0$ contains strictly more cells of $F_0$ than level $l$, or exactly as many with
$l \le l'$; and $c_0$ is a cell of $F_0$ in level $l$ whose column is at most the column of every
cell of $F_0$ in level $l$.

## Sources

- Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024), Article A58, Section 4 (choice of the level `l` and its leftmost rook).
