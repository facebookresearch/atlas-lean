# Deterministic fully dynamic connectivity and MSF with n^{o(1)} worst-case update time

There are deterministic algorithms for fully dynamic connectivity and for fully dynamic minimum spanning forest on $n$-vertex graphs whose worst-case update time is $n^{o(1)}$. Being deterministic, they work against adaptive adversaries.

## Proof sketch

The randomized ingredient of the subpolynomial MSF framework is the expander decomposition, computed by the randomized cut-matching game. Replacing it by the deterministic almost-linear-time balanced cut algorithm, which either finds a balanced sparse cut or certifies a large high-conductance subgraph, yields a deterministic expander decomposition with $n^{o(1)}$ loss. Pruning is already deterministic, so plugging both into the framework gives the deterministic worst-case bound.

## Depends on

- [Fully dynamic connectivity, spanning forest and minimum spanning forest problems](fully-dynamic-connectivity-problems.md)
- [Oblivious and adaptive adversaries; amortized and worst-case update time](adversary-and-update-time-models.md)

## Proof depends on

- [Saranurak-Wang expander pruning under online edge deletions](../../../../GraphTheory/graph-families-and-operations/expander-decomposition-and-pruning/expander-pruning-theorem.md)
- [Deterministic almost-linear-time balanced cut with high-conductance certificates](../../../../GraphTheory/graph-families-and-operations/expander-decomposition-and-pruning/deterministic-balanced-cut-theorem.md)
- [Las Vegas dynamic minimum spanning forest with n^{o(1)} worst-case update time](nsw-subpolynomial-msf.md)

## Sources

- Julia Chuzhoy, Yu Gao, Jason Li, Danupon Nanongkai, Richard Peng, Thatchaphol Saranurak, "A Deterministic Algorithm for Balanced Cut with Applications to Dynamic Connectivity, Flows, and Beyond", FOCS (2020), arXiv:1910.08025.
- Danupon Nanongkai, Thatchaphol Saranurak, Christian Wulff-Nilsen, "Dynamic Minimum Spanning Forest with Subpolynomial Worst-case Update Time", FOCS (2017), arXiv:1708.03962.
