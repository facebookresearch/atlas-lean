# Funnel hashing layout

Let $1/n \le \delta \le 1/2$ with $\delta n$ an integer, so that $\log \delta^{-1}$ is bounded below by a positive constant. *Funnel hashing* splits the array into a sequence of levels $A_1, \dots, A_\alpha$ with $\alpha = \Theta(\log \delta^{-1})$, whose sizes decrease geometrically by a constant factor, followed by a special overflow array $A_{\alpha+1}$ of $\Theta(\delta n)$ slots. Each level $A_i$ is divided into buckets of size $\beta = \Theta(\log \delta^{-1})$. To insert $x$, for $i = 1, \dots, \alpha$ in order the key hashes to a uniformly random bucket of $A_i$ and takes the first free slot of that bucket if there is one; if all $\alpha$ buckets tried are full, $x$ is inserted into $A_{\alpha+1}$ by a two-choice probing scheme using $O(\log \log n)$ probes. Every key uses the first free slot of its probe sequence, so funnel hashing is greedy.

## Depends on

- [Greedy open addressing and uniform probing](greedy-open-addressing-and-uniform-probing.md)

## Sources

- Martín Farach-Colton, Andrew Krapivin, William Kuszmaul, "Optimal Bounds for Open Addressing Without Reordering", FOCS (2024), arXiv:2501.02305.
