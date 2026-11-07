# Bitonic merger

The bitonic merger on the block of wires $[b, b + 2^k)$ is the list of
comparators defined by recursion on $k$. For $k = 0$ it is empty. On the block $[b, b + 2^{k+1})$
it is the half-cleaner on $[b, b + 2^{k+1})$, followed by the bitonic merger on $[b, b + 2^k)$,
followed by the bitonic merger on $[b + 2^k, b + 2^{k+1})$.

This is CLRS's `BITONIC-SORTER`.
