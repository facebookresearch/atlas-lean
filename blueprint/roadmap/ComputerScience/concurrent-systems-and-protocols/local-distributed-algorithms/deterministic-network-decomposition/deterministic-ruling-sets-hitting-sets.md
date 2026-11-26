# Deterministic ruling sets and hitting sets in polylogarithmic time

Let $G = (V, E)$ be a simple connected graph with $n$ vertices and maximum degree $\Delta$, whose vertices carry distinct identifiers from $\{1, \dots, n^{O(1)}\}$. An $(\alpha, \beta)$-ruling set is a set $R \subseteq V$ whose vertices are pairwise at distance at least $\alpha$ and such that every vertex is within distance $\beta$ of $R$; a maximal independent set is a $(2, 1)$-ruling set. There is a deterministic LOCAL algorithm computing a $(2, O(\log\log n))$-ruling set in $\tilde O(\log n)$ rounds, and there are deterministic polylogarithmic-round algorithms computing hitting sets (a set meeting every vertex's neighbourhood of size at least $k$, of size $O(n \log n / k)$) and spanners with $O(\log n)$ stretch and $\tilde O(n)$ edges.

## Proof sketch

The ruling set algorithm runs $O(\log\log\Delta)$ stages, each sparsifying the current set $W$ (initially $V$). Within a stage, repeated deterministic sampling (Ghaffari–Grunau, Corollary 4.2: derandomized hitting-set sampling followed by removal of sampled vertices with too many sampled neighbours) yields a subset of $W$ that dominates all of $W$ and has maximum induced degree at most $\Delta_W^{0.9}$, where $\Delta_W$ is the maximum degree of $G[W]$; this subset replaces $W$, so each stage adds at most $1$ to the domination distance. Once the induced degree is bounded by a constant, a maximal independent set of $G[W]$, computed in $O(\log^* n)$ rounds, finishes the construction, giving an independent set within distance $O(\log\log\Delta) \le O(\log\log n)$ of every vertex. Hitting sets and spanners derandomize sampling arguments whose analyses need only pairwise independence, using conditional expectations over clusters of a network decomposition.

## Depends on

- [The CONGEST model of distributed computing](the-congest-model.md)
- [The LOCAL model](../../distributed-execution-models/the-local-model.md)

## Proof depends on

- [Faster deterministic network decomposition in O(log^5 n) rounds](faster-deterministic-network-decomposition.md)
- [Network decomposition with weak or strong diameter](network-decomposition-weak-strong-diameter.md)

## Sources

- M. Ghaffari, C. Grunau, B. Haeupler, S. Ilchi, V. Rozhoň, "Improved Distributed Network Decomposition, Hitting Sets, and Spanners, via Derandomization", SODA 2023, arXiv:2209.11669.
- M. Ghaffari, C. Grunau, "Near-Optimal Deterministic Network Decomposition and Ruling Set, and Improved MIS", FOCS 2024, arXiv:2410.19516.
