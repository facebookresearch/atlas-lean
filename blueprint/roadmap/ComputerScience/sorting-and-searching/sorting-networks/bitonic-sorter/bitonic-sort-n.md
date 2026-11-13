# Batcher's bitonic sorter on a block of wires

A comparator $(i, j)$ puts the minimum of
the values on wires $i$ and $j$ on wire $i$ and the maximum on wire $j$. Batcher's bitonic sorter
on the block of wires $[b, b + 2^k)$ is the list of comparators defined by recursion on $k$. For
$k = 0$ it is empty. On the block $[b, b + 2^{k+1})$ it is Batcher's bitonic sorter on
$[b, b + 2^k)$, followed by Batcher's bitonic sorter on $[b + 2^k, b + 2^{k+1})$ with every
comparator $(i, j)$ replaced by $(j, i)$, followed by the bitonic merger on $[b, b + 2^{k+1})$.

Reversing the comparators makes the second half sort downwards, so the merger receives a bitonic
sequence. (CLRS's `SORTER` instead sorts both halves up and uses `MERGER`.)
