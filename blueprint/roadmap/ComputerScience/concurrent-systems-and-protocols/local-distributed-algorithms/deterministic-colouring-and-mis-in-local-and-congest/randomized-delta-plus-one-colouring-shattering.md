# Randomized (Delta+1)-colouring in O(log* n) plus deterministic time on polylog-size instances

Let $G = (V, E)$ be a simple connected graph with $n$ vertices and maximum degree $\Delta$, whose vertices carry distinct identifiers from $\{1, \dots, n^{O(1)}\}$. There is a randomized LOCAL algorithm for $(\Delta + 1)$-list colouring, in particular for $(\Delta + 1)$-colouring, that runs in $O(\log^* n) + O\bigl(\mathrm{Det}_{\deg+1}(\mathrm{poly}\log n)\bigr)$ rounds with high probability, where $\mathrm{Det}_{\deg+1}(N)$ is the deterministic complexity of $(\deg+1)$-list colouring on $N$-vertex graphs. With deterministic $(\deg+1)$-list colouring in $O(\log^2 \Delta \log N)$ rounds this gives $O(\log^3 \log n)$ rounds.

## Proof sketch

Decompose the graph hierarchically by local sparsity, with about $\log\log\Delta$ layers of increasingly strict density thresholds, into sparse vertices and dense almost-cliques. One round of random colour trials colours a constant fraction of the vertices and gives every vertex of a sparse layer many excess colours. The dense blocks, grouped into $O(1)$ classes by size and layer, are then coloured by synchronized random colour trials inside each block, so that the vertices of a block avoid conflicts with each other; all these steps take $O(\log^* \Delta)$ rounds. The vertices left uncoloured fall into $O(1)$ classes, each inducing either a bounded-degree graph, coloured deterministically in $O(\log^* n)$ rounds, or, by the graph shattering lemma, components of $\mathrm{poly}\log n$ size with high probability, which form $(\deg+1)$-list colouring instances finished by the deterministic algorithm.

## Depends on

- [The (deg + 1)-list-coloring problem (D1LC)](../../../randomized-algorithms/sketching-streaming-and-sublinear-algorithms/palette-sparsification-and-sublinear-coloring/degree-plus-one-list-coloring.md)
- [The LOCAL model](../../distributed-execution-models/the-local-model.md)

## Proof depends on

- [Graph shattering after a randomized pre-shattering phase](graph-shattering-lemma.md)
- [Deterministic (Delta+1)-colouring in O(log^2 Delta log n) rounds without network decomposition](deterministic-delta-plus-one-colouring-log-squared.md)

## Sources

- Y.-J. Chang, W. Li, S. Pettie, "Distributed (Delta+1)-Coloring via Ultrafast Graph Shattering", STOC 2018; SIAM Journal on Computing 49(3) (2020), arXiv:1711.01361, abstract and Section 2.4.
