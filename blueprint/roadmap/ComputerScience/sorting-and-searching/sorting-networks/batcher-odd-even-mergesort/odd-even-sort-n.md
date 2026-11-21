# Batcher's odd-even merge sort

For $k \in \mathbb{N}$, odd-even merge sort on wires
$0, \dots, 2^k - 1$ is the comparator list defined by recursion on $k$. For $k = 0$ it is empty.
For $k + 1$ it is the sorter for $k$ (sorting wires $0, \dots, 2^k - 1$), followed by the sorter
for $k$ with each wire $i$ renamed to $2^k + i$ (sorting wires $2^k, \dots, 2^{k+1} - 1$),
followed by Batcher's odd-even merger on $2^{k+1}$ wires.
