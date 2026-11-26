# Polylogarithmic-time deterministic network decomposition

Let $G = (V, E)$ be a simple connected graph with $n$ vertices and maximum degree $\Delta$, whose vertices carry distinct identifiers from $\{1, \dots, n^{O(1)}\}$. There is a deterministic distributed algorithm that computes a network decomposition with $O(\log n)$ colours and weak diameter $O(\log^3 n)$ in $\mathrm{poly}(\log n)$ rounds, using messages of $O(\log n)$ bits (so in CONGEST). Combined with the completeness of network decomposition, this gives

$$
\mathrm{P}\text{-}\mathrm{LOCAL} = \mathrm{P}\text{-}\mathrm{SLOCAL} = \mathrm{P}\text{-}\mathrm{RLOCAL}
$$

for problems whose solutions can be checked deterministically in polylogarithmic rounds; in particular maximal independent set and $(\Delta+1)$-colouring have deterministic polylogarithmic-round algorithms.

## Proof sketch

Construct each colour class in $O(\log n)$ phases indexed by the bits of the identifiers. In phase $i$, clusters are labelled red or blue according to bit $i$ of their label; blue vertices adjacent to red clusters repeatedly propose to join a red cluster, and a red cluster accepts all proposals if they amount to at least a $1/(2\log n)$ fraction of its size, otherwise it rejects them and those blue vertices are deleted (killed) from this colour class. Each phase separates red and blue clusters, the growth condition bounds cluster radii by $O(\log^2 n)$ per phase, and only an $O(1/\log n)$ fraction of vertices is killed per phase, so each colour class covers half of the remaining vertices.

## Depends on

- [Network decomposition with weak or strong diameter](network-decomposition-weak-strong-diameter.md)
- [The CONGEST model of distributed computing](the-congest-model.md)
- [The SLOCAL model and its polylogarithmic class](the-slocal-model.md)

## Proof depends on

- [Network decomposition is complete for polylogarithmic sequential locality](network-decomposition-slocal-complete.md)

## Sources

- V. Rozhoň, M. Ghaffari, "Polylogarithmic-Time Deterministic Network Decomposition and Distributed Derandomization", STOC 2020, arXiv:1907.10937.
