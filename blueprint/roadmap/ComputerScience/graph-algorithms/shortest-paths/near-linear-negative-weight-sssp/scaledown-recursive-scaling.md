# ScaleDown: halving the most negative weight in expected O(m log^3 n log Delta) time

There is a randomized algorithm $\mathrm{ScaleDown}(G,\Delta,B)$ with the following guarantees. Input: a directed graph $G=(V,E,w)$ with integer weights, constant out-degree at every vertex, a positive integer $B$ with $w(e)\ge -2B$ for all $e$, and an integer $\Delta\ge 1$ such that, if $G$ has no negative cycle, $\eta(G^B)\le\Delta$. Output: if it terminates, an integral price function $\phi$ with $w_\phi(e)\ge -B$ for every $e\in E$ (correct whether or not $G$ has a negative cycle). Running time: if $G$ has no negative cycle, the expected running time is $O(m\log^3 n\log\Delta)$.

The algorithm runs four phases: (0) $E^{rem}\leftarrow\mathrm{LowDiamDecomposition}(G^B_{\ge 0},\Delta B/2)$ and compute the strongly connected components $V_i$ of $G^B\setminus E^{rem}$; (1) recursively call $\mathrm{ScaleDown}(\bigcup_i G[V_i],\Delta/2,B)$; (2) apply FixDAGEdges to the remaining inter-component edges; (3) run ElimNeg from the dummy source to repair the edges of $E^{rem}$.

## Proof sketch

Correctness is immediate: Phase 3 returns $\phi$ making $w^B_\phi\ge 0$, and $w^B\le w+B$ gives $w_\phi\ge -B$. For the running time, the halving lemma justifies the recursive call with parameter $\Delta/2$, so the recursion depth is $O(\log\Delta)$. After Phases 1-2 the only negative edges of $G^B_{\phi_2}$ lie in $E^{rem}$, so $\eta_{(G^B_s)_{\phi_2}}(v)\le |P_{G^B}(v)\cap E^{rem}|+1$, whose expectation is $O(\log^2 n)$ by the sparse-hitting lemma; ElimNeg then costs $O(m\log^3 n)$ in expectation per level, dominating the $O(m\log^2 n+n\log^3 n)$ decomposition.

## Depends on

- [The negative-edge count eta of shortest paths and the B-shifted graph](negative-edge-count-eta.md)
- [Price functions, reduced edge weights, and valid reweightings of a directed graph](price-functions-and-reduced-weights.md)
- [Weak and strong directed low-diameter decompositions with overhead rho](directed-low-diameter-decomposition.md)

## Proof depends on

- [FixDAGEdges: a linear-time price function for graphs whose negative edges join parts of an acyclic condensation](fix-dag-edges.md)
- [ElimNeg: the Dijkstra-Bellman-Ford hybrid runs in time proportional to the negative-edge counts of shortest paths](elimneg-dijkstra-bellman-ford-hybrid.md)
- [A directed LDD hits eta-bounded shortest paths O(log^2 n) times in expectation](ldd-sparse-hitting-eta-bounded-paths.md)
- [Inside components of small weak diameter the B-shifted negative-edge count halves](scc-halving-of-eta.md)

## Sources

- Aaron Bernstein, Danupon Nanongkai, Christian Wulff-Nilsen, "Negative-Weight Single-Source Shortest Paths in Near-linear Time", FOCS (2022), arXiv:2203.03456.
