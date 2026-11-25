# The $m$-weight of a file placement

For a natural number $m$ and a finite set $F$ of cells
$(i, j)$ (column $i$, row $j$), let $f_j$ be the number of cells of $F$ in row $j$. The $m$-weight
of $F$ is $\mathrm{wt}_m(F) = \prod_j 1\downarrow_{f_j, m}$, the product over the rows $j$ that
contain a cell of $F$, where $x\downarrow_{k, m} = \prod_{i < k} (x - m i)$ is the $m$-falling
factorial.

## Sources

- Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024), Article A58, Section 3.1 (definition of `wt_m`).
