# Deterministic ruling sets and hitting sets in polylogarithmic time

Let $G = (V, E)$ be a simple connected graph with $n$ vertices and maximum degree $\Delta$, whose vertices carry distinct identifiers from $\{1, \dots, n^{O(1)}\}$. An $(\alpha, \beta)$-ruling set is a set $R \subseteq V$ whose vertices are pairwise at distance at least $\alpha$ and such that every vertex is within distance $\beta$ of $R$; a maximal independent set is a $(2, 1)$-ruling set. There is a deterministic LOCAL algorithm that, given an upper bound $\Delta$ on the maximum degree known to all vertices, computes in $\tilde O(\log n)$ rounds an independent set within distance $O(\log\log \Delta)$ of every vertex, in particular a $(2, O(\log\log n))$-ruling set, and there are deterministic polylogarithmic-round algorithms computing hitting sets (a set meeting every vertex's neighbourhood of size at least $k$, of size $O(n \log n / k)$) and spanners with $O(\log n)$ stretch and $\tilde O(n)$ edges.

## Proof sketch

The ruling set algorithm runs $O(\log\log\Delta)$ stages, each sparsifying the current set $W$ (initially $V$) while moving at most one step further from it. Its tool (Ghaffari–Grunau, Corollary 4.2) is a derandomized hitting-set sampling followed by removal of sampled vertices with too many sampled neighbours: in $\tilde O(\log \Delta_W) \log^* n$ rounds, where $\Delta_W$ bounds the maximum degree of $G[W]$, it returns $W' \subseteq W$ of maximum induced degree at most $\Delta_W^{0.9}$ such that all but at most $N_{\mathrm{high}}/\Delta_W$ of the vertices of $W$ with at least $\Delta_W^{0.9}$ neighbours in $W$ have a neighbour in $W'$, where $N_{\mathrm{high}}$ is a known bound on their number. It does not dominate all of $W$. A stage therefore repeats it $O(\log_{\Delta_W} n)$ times with geometrically shrinking exception budgets: each time the sampled set is added to the stage output and removed from $W$ together with its neighbours, so the remainder shrinks until no vertex of $W$ has $\Delta_W^{0.9}$ neighbours left in $W$; the remaining vertices are then added to the output. The output dominates the stage's $W$ and has maximum induced degree at most $\Delta_W^{0.9}$, and it replaces $W$. Once the induced degree is bounded by a constant, a maximal independent set of $G[W]$, computed in $O(\log^* n)$ rounds, finishes the construction. Hitting sets and spanners derandomize sampling arguments, split into $O(\log n)$ steps whose analyses need only pairwise independence, using conditional expectations over clusters of a network decomposition.

## Depends on

- [The CONGEST model of distributed computing](the-congest-model.md)
- [The LOCAL model](../../distributed-execution-models/the-local-model.md)

## Proof depends on

- [Faster deterministic network decomposition in O(log^5 n) rounds](faster-deterministic-network-decomposition.md)
- [Network decomposition with weak or strong diameter](network-decomposition-weak-strong-diameter.md)

## Sources

- M. Ghaffari, C. Grunau, B. Haeupler, S. Ilchi, V. Rozhoň, "Improved Distributed Network Decomposition, Hitting Sets, and Spanners, via Derandomization", SODA 2023, arXiv:2209.11669, Theorem 1.2 and Corollary 1.3.
- M. Ghaffari, C. Grunau, "Near-Optimal Deterministic Network Decomposition and Ruling Set, and Improved MIS", FOCS 2024, arXiv:2410.19516, Theorem 4.1 and Corollary 4.2.
