# Deterministic recovery from an approximate signal

Let $M$ be the signed adjacency matrix of a graph containing a clique $S$ of size $k$. If $\|M - \mathbf{1}_S\mathbf{1}_S^\top\|_{\mathrm{op}} \le k/16$, then the $k$ largest coordinates (in absolute value) of a suitable top eigenvector or power-iteration vector form a set $T$ missing at most $k/16$ vertices of $S$. If moreover every vertex outside $S$ has at most $5k/8$ neighbours in $S$, then the **degree cleanup** $\{v : v \text{ has at least } 3k/4 \text{ neighbours in } T\}$ equals $S$ exactly.

## Proof sketch

Davis-Kahan-type perturbation: the unit vector aligned with $\mathbf{1}_S/\sqrt{k}$ is within small angle of the computed vector, which bounds the number of misplaced coordinates. Vertices of $S$ have at least $k - k/16 - k/16$ neighbours in $T$, outsiders at most $5k/8 + k/16$.

## Depends on

- [The planted clique model and recovery](planted-clique-model.md)

## Sources

- N. Alon, M. Krivelevich and B. Sudakov, "Finding a Large Hidden Clique in a Random Graph", Random Structures & Algorithms 13(3-4), 1998.
