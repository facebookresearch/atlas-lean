# Randomized (Delta+1)-colouring in O(log* n) plus deterministic time on polylog-size instances

Let $G = (V, E)$ be a simple connected graph with $n$ vertices and maximum degree $\Delta$, whose vertices carry distinct identifiers from $\{1, \dots, n^{O(1)}\}$. There is a randomized LOCAL algorithm for $(\Delta + 1)$-colouring that runs in $O(\log^* n) + O\bigl(\mathrm{Det}_{\deg+1}(\mathrm{poly}\log n)\bigr)$ rounds with high probability, where $\mathrm{Det}_{\deg+1}(N)$ is the deterministic complexity of $(\deg+1)$-list colouring on $N$-vertex graphs. With deterministic $(\deg+1)$-list colouring in $O(\log^2 \Delta \log N)$ rounds this gives $O(\log^3 \log n)$ rounds.

## Proof sketch

Decompose the graph by local sparsity into sparse vertices and dense almost-cliques. Sparse vertices obtain excess colours through a single round of random colour trials and are then coloured quickly; almost-cliques are coloured by a synchronized random permutation within each clique, which succeeds for all but a $\Delta^{-\Omega(1)}$ fraction of vertices in $O(\log^* n)$ rounds. The graph shattering lemma bounds the uncoloured components by $\mathrm{poly}\log n$ size, and the deterministic list-colouring algorithm finishes them.

## Depends on

- [The (deg + 1)-list-coloring problem (D1LC)](../../../randomized-algorithms/palette-sparsification-and-sublinear-coloring/degree-plus-one-list-coloring.md)
- [The LOCAL model](../../distributed-execution-models/the-local-model.md)

## Proof depends on

- [Graph shattering after a randomized pre-shattering phase](graph-shattering-lemma.md)
- [Deterministic (Delta+1)-colouring in O(log^2 Delta log n) rounds without network decomposition](deterministic-delta-plus-one-colouring-log-squared.md)

## Sources

- Y.-J. Chang, W. Li, S. Pettie, "Distributed (Delta+1)-Coloring via Ultrafast Graph Shattering", STOC 2018; SIAM Journal on Computing 49(3) (2020), arXiv:1711.01361.
