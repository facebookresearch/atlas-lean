# Cost balance for stack operation sequences

For every stack $S$ and every finite sequence
$\sigma$ of stack operations, if running $\sigma$ on $S$ succeeds with final stack $F$, then the
cost of the run plus the number of elements of $F$ equals the number of elements of $S$ plus
twice the number of PUSH operations in $\sigma$.
