# Deterministic global and Steiner minimum cut via isolating cuts (Li-Panigrahi)

For every fixed $\varepsilon > 0$ there is a deterministic algorithm that, given an undirected graph $G = (V, E, w)$ with $n$ vertices, $m$ edges and polynomially bounded positive integer weights, and terminals $R \subseteq V$ with $|R| \ge 2$, computes an $R$-Steiner minimum cut (in particular, for $R = V$, a global minimum cut) using $(\log n)^{O(1/\varepsilon^4)}$ max-flow calls and $O(m^{1+\varepsilon})$ additional time. With the deterministic maximum-flow algorithms available at the time this gives running time $\tilde O(m \cdot \min(\sqrt m, n^{2/3}))$ for weighted graphs and $m^{4/3+o(1)}$ for unweighted multigraphs, the first improvement over the $\tilde O(mn)$ deterministic bound for global minimum cut.

## Proof sketch

The random terminal sampling of the Monte Carlo algorithm is replaced by a deterministic decomposition: an expander-decomposition-based recursion splits the terminal set into groups in which every Steiner minimum cut either has few terminals on its small side, so that a deterministically chosen family of sub-terminal sets isolates it, or is captured by a smaller instance. Each level applies the isolating cut lemma, which costs $O(\log n)$ max-flow calls, and the recursion depth and branching depend only on $\varepsilon$, giving the $(\log n)^{O(1/\varepsilon^4)}$ bound.

## Depends on

- [Steiner minimum cuts of a terminal set](steiner-minimum-cut.md)
- [Maximum-flow oracles and the max-flow call model for cut problems](max-flow-oracle-call-model.md)

## Proof depends on

- [Isolating cut lemma with logarithmically many max-flow calls](isolating-cut-lemma.md)

## Sources

- Jason Li, Debmalya Panigrahi, "Deterministic Min-cut in Poly-logarithmic Max-flows", FOCS (2020), arXiv:2111.02008.
- Matthew Ding, Jason Li, "Deterministic Minimum Steiner Cut in Maximum Flow Time", ESA (2024), LIPIcs, doi:10.4230/LIPIcs.ESA.2024.46, arXiv:2312.16415.
