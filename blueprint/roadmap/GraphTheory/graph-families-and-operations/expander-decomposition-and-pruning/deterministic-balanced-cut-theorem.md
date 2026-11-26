# Deterministic almost-linear-time balanced cut with high-conductance certificates

There is a deterministic algorithm that, given an $n$-vertex $m$-edge undirected graph $G$ and a parameter $1 \le r \le O(\log n)$, computes a $(\log m)^{r^2}$-approximation for Minimum Balanced Cut in time

$$
O\bigl(m^{1 + O(1/r) + o(1)} \cdot (\log m)^{O(r^2)}\bigr).
$$

More strongly, given a target value, it either returns a balanced cut whose value is within that approximation factor of the target, or certifies that no balanced cut of the target value exists by exhibiting a large subgraph of $G$ of high conductance. In particular one obtains a $(\log m)^{1/\epsilon}$-approximation in time $m^{1 + O(1/\sqrt{\epsilon})}$ for every constant $\epsilon > 0$, and deterministic algorithms with similar guarantees for Sparsest Cut and Lowest-Conductance Cut.

## Proof sketch

The algorithm derandomizes the cut-matching game: the cut player's random projection is replaced by a recursive call that finds a balanced sparse cut, or certifies expansion, in the current union of matchings, which has fewer edges. The recursion is organized into $r$ levels, each contracting the problem size by a factor $m^{1/r}$ and losing a $(\log m)^{O(r)}$ factor in approximation. Each level's matching player is implemented by deterministic flow routing, and when the game ends without a balanced cut the embedded expander certifies a large high-conductance subgraph.

## Depends on

- [The Khandekar-Rao-Vazirani cut-matching game](krv-cut-matching-game.md)
- [Cut conductance, phi-expanders and degree-preserving induced subgraphs](conductance-and-phi-expanders.md)

## Proof depends on

- [Random-projection cut strategies win the cut-matching game in O(log^2 n) rounds](krv-cut-strategy-theorem.md)

## Sources

- Julia Chuzhoy, Yu Gao, Jason Li, Danupon Nanongkai, Richard Peng, Thatchaphol Saranurak, "A Deterministic Algorithm for Balanced Cut with Applications to Dynamic Connectivity, Flows, and Beyond", FOCS (2020), arXiv:1910.08025.
