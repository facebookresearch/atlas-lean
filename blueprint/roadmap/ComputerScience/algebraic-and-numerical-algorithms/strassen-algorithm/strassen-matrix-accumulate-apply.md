# Entries of Strassen's matrix accumulator

Let $R$ be a non-unital, non-associative ring.
For every $k \ge 0$, all $2^k \times 2^k$ matrices $A$, $B$, $C$ over $R$ and all indices
$i, j$, the $(i, j)$ entry of the matrix returned by Strassen's accumulator on $A$, $B$, $C$ is
$C_{ij} + \sum_{t} A_{it} B_{tj}$, the sum running over all $2^k$ indices $t$.
