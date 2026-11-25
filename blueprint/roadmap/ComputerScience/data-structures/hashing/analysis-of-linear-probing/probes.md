# Probes of a linear-probing insertion

The number of probes of an insertion with hash address $h$ into a cyclic table whose occupied cells
form $S$ is its [displacement](displacement.md) plus one. When the table is not full, this is, in
Knuth's 1963 description of the algorithm, the number of times the comparison step "if $x_j = 0$,
set $x_j = 1$ and stop" is executed: once for each occupied cell passed over, and once for the
empty cell that receives the item. When all $N$ cells are occupied there is no empty cell, and the
count is $N + 1$.

## Sources

- D. E. Knuth, "Notes on 'open' addressing", 22 July 1963, typeset by H. Prodinger in 1997,
  Section 1: https://jeffe.cs.illinois.edu/teaching/datastructures/2011/notes/knuth-OALP.pdf
