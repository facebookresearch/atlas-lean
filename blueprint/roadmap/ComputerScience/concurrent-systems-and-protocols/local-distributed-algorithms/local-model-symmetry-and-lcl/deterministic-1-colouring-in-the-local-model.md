# Deterministic (Δ + 1)-colouring in the LOCAL model

On finite graphs of maximum degree at most $\Delta \ge 1$ with initial proper colours below $C$ (for instance distinct identifiers), a deterministic LOCAL algorithm combining Cole–Vishkin-type colour reduction, Kuhn–Wattenhofer colour compression and greedy one-round reductions (in which every vertex whose colour is a local maximum recolours to the smallest free colour) computes a proper $(\Delta + 1)$-colouring within $O(\Delta^2 + \log^* C)$ rounds: colour reduction reaches $O(\Delta^2)$ colours in $O(\log^* C)$ rounds, and each greedy round reduces the number of colours $x$ to $\max(x - 1, \Delta + 1)$ (Hirvonen and Suomela, Section 4.8 and Lemma 4.1). Replacing the greedy phase by additive-group colour reduction gives $O(\Delta + \log^* n)$ rounds from identifiers (Hirvonen and Suomela, Theorem 4.8).

## Proof sketch

Reduce identifiers to $O(\Delta^2)$ colours in $O(\log^* C)$ rounds by deterministic coin tossing on neighbour pairs, then eliminate one colour class above $\Delta + 1$ per round: local maxima form an independent set and each finds a free colour among $\Delta + 1$.

## Depends on

- [The LOCAL model](../../distributed-execution-models/the-local-model.md)

## Proof depends on

- [Cole–Vishkin coloring in O(log* n) rounds](../colevishkin-coloring-in-o-log-n-rounds.md)
- [A Cole–Vishkin step keeps the coloring proper](../../../parallel-algorithms/cole-vishkin-deterministic-coin-tossing/cv-color-proper.md)

## Sources

- Richard Cole and Uzi Vishkin, "Deterministic Coin Tossing with Applications to Optimal Parallel List Ranking", Information and Control, 1986.
- Andrew V. Goldberg, Serge A. Plotkin and Gregory E. Shannon, "Parallel Symmetry-Breaking in Sparse Graphs", SIAM Journal on Discrete Mathematics, 1988.
- Fabian Kuhn and Roger Wattenhofer, "On the Complexity of Distributed Graph Coloring", Proceedings of the Twenty-Fifth Annual ACM Symposium on Principles of Distributed Computing (PODC 2006), 2006.
- Juho Hirvonen and Jukka Suomela, "Distributed Algorithms 2020", Online textbook, Aalto University, 2020, Lemma 4.1, Section 4.8 and Theorem 4.8.
