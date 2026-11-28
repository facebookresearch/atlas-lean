# Deterministic Steiner minimum cut in maximum-flow time (Ding-Li)

There is a deterministic algorithm that, given an undirected graph $G = (V, E, w)$ with $n$ vertices, $m$ edges and polynomially bounded positive integer weights, and a terminal set $R \subseteq V$ with $|R| \ge 2$, computes an $R$-Steiner minimum cut using $(\log n)^{O(1)}$ calls to a maximum-flow oracle on undirected weighted graphs with $O(n)$ vertices and $O(m)$ edges, plus $\tilde O(m)$ additional time. Consequently, any deterministic $\tilde O(m)$-time $s$-$t$ maximum-flow algorithm would yield a deterministic $\tilde O(m)$-time algorithm for Steiner minimum cut.

## Proof sketch

The proof replaces the $O(m^{1+\varepsilon})$-time terminal decomposition of the Li-Panigrahi algorithm by a deterministic decomposition of the terminal set that generalizes $s$-strong partitions: it splits the terminals into polylogarithmically many groups such that, for each Steiner minimum cut, some group meets its small side in a set that a deterministic family of isolating-cut instances can isolate. Each instance is solved with the isolating cut lemma, so the whole algorithm reduces to polylogarithmically many max-flow calls plus near-linear bookkeeping.

## Depends on

- [Steiner minimum cuts of a terminal set](steiner-minimum-cut.md)
- [Maximum-flow oracles and the max-flow call model for cut problems](max-flow-oracle-call-model.md)

## Proof depends on

- [Deterministic global and Steiner minimum cut via isolating cuts (Li-Panigrahi)](li-panigrahi-deterministic-steiner-mincut.md)
- [Isolating cut lemma with logarithmically many max-flow calls](isolating-cut-lemma.md)

## Sources

- Matthew Ding, Jason Li, "Deterministic Minimum Steiner Cut in Maximum Flow Time", ESA (2024), LIPIcs, doi:10.4230/LIPIcs.ESA.2024.46, Theorem 1, arXiv:2312.16415.
- Jason Li, Debmalya Panigrahi, "Deterministic Min-cut in Poly-logarithmic Max-flows", FOCS (2020), arXiv:2111.02008.
