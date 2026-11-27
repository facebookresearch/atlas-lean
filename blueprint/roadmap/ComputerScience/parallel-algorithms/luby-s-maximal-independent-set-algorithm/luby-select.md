# Selection step of Luby's algorithm

For a graph on vertices $\{0, \dots, n-1\}$, priorities $\pi(v) \in \mathbb{N}$ and a set of active vertices, the selection step of a round of Luby's algorithm picks the active vertices whose key $\pi(v)\,n + v$ is smaller than the key of every active neighbor; ties between equal priorities are broken by vertex index.

## Sources

- M. Luby, "A simple parallel algorithm for the maximal independent set problem", *SIAM Journal on Computing* 15 (1986).
