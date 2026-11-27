# Polylogarithmic-time deterministic network decomposition

Let $G = (V, E)$ be a simple connected graph with $n$ vertices and maximum degree $\Delta$, whose vertices carry distinct identifiers from $\{1, \dots, n^{O(1)}\}$. There is a deterministic distributed algorithm that computes a network decomposition with $O(\log n)$ colours and weak diameter $O(\log^3 n)$ in $\mathrm{poly}(\log n)$ rounds, using messages of $O(\log n)$ bits (so in CONGEST). Combined with the completeness of network decomposition, this gives

$$
\mathrm{P}\text{-}\mathrm{LOCAL} = \mathrm{P}\text{-}\mathrm{SLOCAL} = \mathrm{P}\text{-}\mathrm{RLOCAL}
$$

for problems whose solutions can be checked deterministically in polylogarithmic rounds; in particular maximal independent set and $(\Delta+1)$-colouring have deterministic polylogarithmic-round algorithms.

## Proof sketch

Construct each colour class in $b = O(\log n)$ phases indexed by the bits of the identifiers, starting with every remaining vertex as its own cluster. In phase $i$, clusters are labelled red or blue according to bit $i$ of their identifier. Step by step, each red vertex adjacent to a blue cluster requests to join one; a blue cluster accepts all requests if they amount to at least a $1/(2b)$ fraction of its size, growing by one hop, and otherwise rejects them, and those red vertices are deleted (killed) from this colour class while the cluster stops growing for the phase. A cluster can accept only $O(b \log n)$ times before exceeding $n$ vertices, so radii grow by $O(\log^2 n)$ per phase; at most a $1/(2b)$ fraction of the vertices dies per phase; and at the end of the phase no red cluster is adjacent to a blue one. After $b$ phases adjacent surviving clusters agree on all identifier bits, so they coincide, and at least half of the remaining vertices are clustered.

## Depends on

- [Network decomposition with weak or strong diameter](network-decomposition-weak-strong-diameter.md)
- [The CONGEST model of distributed computing](the-congest-model.md)
- [The SLOCAL model and its polylogarithmic class](the-slocal-model.md)

## Proof depends on

- [Network decomposition is complete for polylogarithmic sequential locality](network-decomposition-slocal-complete.md)

## Sources

- V. Rozhoň, M. Ghaffari, "Polylogarithmic-Time Deterministic Network Decomposition and Distributed Derandomization", STOC 2020, arXiv:1907.10937, Section 1.3 and Section 2.
