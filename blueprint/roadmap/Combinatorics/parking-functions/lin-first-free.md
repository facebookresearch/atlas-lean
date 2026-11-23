# First free cell at or after a hash address

Number the cells of a table $0, 1, \dots, t - 1$ and let $\mathrm{occ}$ be the set of occupied
cells. For a hash address $a$, this is the least free cell $k$ with $a \le k$, or "none" when
every cell from $a$ to $t - 1$ is occupied. "None" is the overflow case of linear probing
without wrap-around: the item would have to run past the last cell.
