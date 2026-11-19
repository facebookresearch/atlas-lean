# Cell taken by a linear-probing insertion

An item with hash address $h$, entered into a cyclic table of $N$ cells whose occupied cells form
$S$, falls into cell $h + d \bmod N$, where $d$ is its [displacement](displacement.md). When the
table is not full this is the first empty cell from $h$ on; when all $N$ cells are occupied,
$d = N$ and the cell is $h$ itself, which is occupied.
