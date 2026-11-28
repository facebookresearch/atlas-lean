# Funnel hashing layout

Let $n \in \mathbb{N}$ and $\delta \in (0, 1/2]$ with $\delta n$ an integer, $\delta n \ge 2$ and $\delta \ge n^{-o(1)}$, the regime of the funnel hashing bounds; $\delta n \ge 2$ is needed for the overflow array below to exist. *Funnel hashing* splits the array into a sequence of levels $A_1, \dots, A_\alpha$ with $\alpha = \Theta(\log \delta^{-1})$, whose sizes decrease geometrically by a constant factor, followed by a special overflow array $A_{\alpha+1}$ with $\lceil \delta n/2 \rceil \le |A_{\alpha+1}| \le \lfloor 3\delta n/4 \rfloor$. Each level $A_i$ is divided into buckets of size $\beta = \Theta(\log \delta^{-1})$. To insert $x$, for $i = 1, \dots, \alpha$ in order the key hashes to a uniformly random bucket of $A_i$ and takes the first free slot of that bucket if there is one; if all $\alpha$ buckets tried are full, $x$ is inserted into $A_{\alpha+1}$, which is split into two halves $B$ and $C$ of equal size up to one slot. First $x$ makes up to $\log \log n$ uniformly random probes into $B$, a uniform probing table, and takes the first free slot found. If all of them are occupied, $x$ goes to $C$, a two-choice table with buckets of $2\log\log n$ slots: it hashes to two buckets and alternates between their slots, so it lands in the emptier one. If both buckets are full the table fails; no bucket of $C$ overflows with probability $1 - 1/\mathrm{poly}(n)$, so every insertion succeeds only with high probability. Every key uses the first free slot of its probe sequence, so funnel hashing is greedy.

## Depends on

- [Greedy open addressing and uniform probing](greedy-open-addressing-and-uniform-probing.md)

## Sources

- Martín Farach-Colton, Andrew Krapivin, William Kuszmaul, "Optimal Bounds for Open Addressing Without Reordering", FOCS (2024), arXiv:2501.02305.
