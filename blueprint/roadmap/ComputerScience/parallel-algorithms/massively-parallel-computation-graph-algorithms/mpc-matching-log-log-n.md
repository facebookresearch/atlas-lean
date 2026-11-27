# Approximate maximum matching in O(log log n) MPC rounds with near-linear memory

In the MPC model with local memory $S = n^{\Omega(1)}$, for every $\varepsilon \in (0, 1/2)$ a $(2 + \varepsilon)$-approximate maximum matching of an $n$-vertex graph can be computed with probability at least $99/100$ in $O\big(((\log\log n)^2 + \max\{\log(n/S), 0\}) \cdot \log(1/\varepsilon)\big)$ rounds, so in $O((\log\log n)^2 \log(1/\varepsilon))$ rounds when $S = \Omega(n)$ (Czumaj et al.). With $\tilde O(n)$ memory per machine this was improved to $O(\log\log n)$ rounds with high probability: an integral $(2 + \varepsilon)$-approximate maximum matching and a $(2 + \varepsilon)$-approximate minimum vertex cover in $O(\log\log n)$ rounds, and a $(1 + \varepsilon)$-approximate maximum matching in $O(\log\log n)\cdot(1/\varepsilon)^{O(1/\varepsilon)}$ rounds, for any constant $\varepsilon > 0$ (Ghaffari et al.). Before these results, the best known upper bound in this regime was $O(\log n)$ rounds.

## Proof sketch

Compress rounds of a centralized or LOCAL fractional matching process: randomly partition vertices among machines so that each machine can simulate many rounds of the process on its induced subgraph, which mimics the global process up to small errors because degrees concentrate. Each phase reduces the maximum degree polynomially (from $\Delta$ to about $\Delta^{1 - \Omega(1)}$), giving $O(\log\log n)$ phases, and the fractional solution is rounded to an integral matching with constant loss.

## Depends on

- [The massively parallel computation model](massively-parallel-computation-model.md)

## Sources

- A. Czumaj, J. Łącki, A. Mądry, S. Mitrović, K. Onak, P. Sankowski, "Round Compression for Parallel Matching Algorithms", STOC 2018; SIAM Journal on Computing 49(5) (2020), arXiv:1707.03478, Corollary 1.2.
- M. Ghaffari, T. Gouleakis, C. Konrad, S. Mitrović, R. Rubinfeld, "Improved Massively Parallel Computation Algorithms for MIS, Matching, and Vertex Cover", PODC 2018, arXiv:1802.08237, Theorem 1.2 and Corollary 1.3.
