# Displacement of a linear-probing insertion

In a cyclic table of $N$ cells whose occupied cells form $S$, the displacement of an item with hash
address $h$ is the number of consecutive occupied cells $h, h + 1, \dots$ (indices modulo $N$) met
before the first empty cell, scanning at most $N$ cells: it is the
[scan with a probe budget](displacement-aux.md) with budget $N$, so it is at most $N$. When the
table is not full it is the distance from $h$ to the first empty cell; when all $N$ cells are
occupied it is $N$.
