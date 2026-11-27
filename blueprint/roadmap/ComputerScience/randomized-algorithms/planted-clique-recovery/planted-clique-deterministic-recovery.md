# Deterministic recovery from an approximate signal

Let $M$ be the signed adjacency matrix of a graph containing a clique $S$ of size $k$. If $\|M - \mathbf{1}_S\mathbf{1}_S^\top\|_{\mathrm{op}} \le k/16$, then for a unit eigenvector $x$ for the largest eigenvalue of $M$, and more generally for every unit vector $x$ with $\|x - \sigma\,\mathbf{1}_S/\sqrt{k}\|_2 \le 1/8$ for some sign $\sigma \in \{\pm 1\}$, the set $T$ of the $k$ largest coordinates of $x$ in absolute value (ties broken arbitrarily) misses at most $k/16$ vertices of $S$. If moreover every vertex outside $S$ has at most $5k/8$ neighbours in $S$, then the **degree cleanup** $\{v : v \text{ has at least } 3k/4 \text{ neighbours in } T\}$ equals $S$ exactly.

## Proof sketch

Write $M = \mathbf{1}_S\mathbf{1}_S^\top + E$ and $u = \mathbf{1}_S/\sqrt{k}$. The largest eigenvalue is $\lambda \ge u^\top M u \ge 15k/16$; projecting $Mx = \lambda x$ onto $u^\perp$ gives $\lambda \sin\theta \le \|E\|_{\mathrm{op}} \le k/16$ for the angle $\theta$ between $x$ and $\pm u$, so $\|x - \sigma u\|_2^2 \le 2\sin^2\theta \le 2/225 < 1/64$. Each pair of a missed vertex of $S$ and a vertex of $T \setminus S$ contributes at least $1/(4k)$ to $\|x - \sigma u\|_2^2$, so at most $k/16$ vertices are missed. Vertices of $S$ have at least $k - k/16 - k/16$ neighbours in $T$, outsiders at most $5k/8 + k/16$.

## Depends on

- [Planted clique model, search and detection problems](../../../GraphTheory/random-graphs/planted-clique/planted-clique-model.md)

## Sources

- N. Alon, M. Krivelevich and B. Sudakov, "Finding a Large Hidden Clique in a Random Graph", Random Structures & Algorithms 13(3-4), 1998.
