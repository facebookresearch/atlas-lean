# Bit-swap pieces sum to the swap permutation matrix

For every $n \in \mathbb{N}$, the [pieces](bit-swap-piece.md) $\Pi_{n,0}, \dots, \Pi_{n,n}$ sum to
the permutation matrix that swaps two $n$-bit strings: for all $n$-bit strings $x, y, u, v$,

$$\sum_{i=0}^{n} \Pi_{n,i}\bigl[(x, y), (u, v)\bigr] =
\begin{cases} 1 & \text{if } u = y \text{ and } v = x, \\ 0 & \text{otherwise.} \end{cases}$$
