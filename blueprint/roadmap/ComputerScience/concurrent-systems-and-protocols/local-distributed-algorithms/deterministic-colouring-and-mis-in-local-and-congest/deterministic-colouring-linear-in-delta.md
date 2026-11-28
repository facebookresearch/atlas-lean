# Deterministic lambda(Delta+1)-colouring trade-off and sublinear-in-Delta (Delta+1)-colouring

Let $G = (V, E)$ be a simple connected graph with $n$ vertices and maximum degree $\Delta$, whose vertices carry distinct identifiers from $\{1, \dots, n^{O(1)}\}$. For every $\lambda \ge 1$ there is a deterministic LOCAL algorithm that computes a proper $\lambda(\Delta + 1)$-colouring in $O(\Delta/\lambda + \log^* n)$ rounds; the case $\lambda = 1$ is the linear-in-$\Delta$ $(\Delta + 1)$-colouring bound $O(\Delta + \log^* n)$. Furthermore, using local conflict colouring, $(\Delta + 1)$-list colouring (and in particular $(\Delta + 1)$-colouring) can be solved in $O(\sqrt{\Delta} \log^{2.5} \Delta + \log^* n)$ rounds, so the dependence on $\Delta$ is sublinear.

## Proof sketch

Compute an $O(\Delta^2)$-colouring by Linial's colour reduction. A recursive procedure then colours a subgraph of maximum degree at most $D$ with $D + 1$ colours: compute a $\lfloor D/2 \rfloor$-defective colouring with $C = O(1)$ colours in $O(\log^* \Delta)$ rounds, recursively colour every colour class (maximum degree at most $\lfloor D/2 \rfloor$) in parallel with $\lfloor D/2 \rfloor + 1$ colours, and combine the two colours into a proper colouring with $C(\lfloor D/2 \rfloor + 1)$ colours. Combining alone uses more than $D + 1$ colours (already two disjoint palettes of $\Delta/2 + 1$ colours give $\Delta + 2$ for even $\Delta$), so a palette-reduction step follows: starting from a proper $B$-colouring with $B > A \ge D + 1$, a proper $A$-colouring is computed in $O(D \log(B/A))$ rounds, here $O(D)$ rounds since $B/A = O(1)$. The running time satisfies $T(D) \le T(\lfloor D/2 \rfloor) + O(D) + O(\log^* \Delta)$, giving $O(\Delta + \log \Delta \log^* \Delta) = O(\Delta)$ after the initial colouring. The $\lambda$ trade-off stops the recursion at degree $\Theta(\Delta/\lambda)$ and keeps the defective colours. For the sublinear bound, local conflict colouring gives each vertex a list and a conflict structure, and an iterative trial procedure, run along a defective colouring, solves it in $O(\sqrt{\Delta}\, \mathrm{polylog}\,\Delta)$ iterations.

## Depends on

- [The (deg + 1)-list-coloring problem (D1LC)](../../../randomized-algorithms/sketching-streaming-and-sublinear-algorithms/palette-sparsification-and-sublinear-coloring/degree-plus-one-list-coloring.md)
- [The LOCAL model](../../distributed-execution-models/the-local-model.md)
- [Deterministic (Δ + 1)-colouring in the LOCAL model](../local-model-symmetry-and-lcl/deterministic-1-colouring-in-the-local-model.md)

## Proof depends on

- [Linial's colour reduction to O(Delta^2) colours in O(log* n) rounds](linial-colour-reduction.md)

## Sources

- L. Barenboim, M. Elkin, F. Kuhn, "Distributed (Delta+1)-Coloring in Linear (in Delta) Time", SIAM Journal on Computing 43(1) (2014); STOC 2009, arXiv:0812.1379.
- P. Fraigniaud, M. Heinrich, A. Kosowski, "Local Conflict Coloring", FOCS 2016, arXiv:1511.01287, Theorem 4.1 and Corollary 4.1.
- F. Kuhn, "Weak Graph Colorings: Distributed Algorithms and Applications", SPAA 2009, Lemma 5.2, Algorithm 3, Lemma 5.3 and Theorem 5.4.
