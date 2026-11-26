# Deterministic ruling sets and hitting sets in polylogarithmic time

Let $G = (V, E)$ be a simple connected graph with $n$ vertices and maximum degree $\Delta$, whose vertices carry distinct identifiers from $\{1, \dots, n^{O(1)}\}$. An $(\alpha, \beta)$-ruling set is a set $R \subseteq V$ whose vertices are pairwise at distance at least $\alpha$ and such that every vertex is within distance $\beta$ of $R$; a maximal independent set is a $(2, 1)$-ruling set. There is a deterministic CONGEST algorithm computing a $(2, O(\log\log n))$-ruling set in $\tilde O(\log n)$ rounds, and there are deterministic polylogarithmic-round algorithms computing hitting sets (a set meeting every vertex's neighbourhood of size at least $k$, of size $O(n \log n / k)$) and spanners with $O(\log n)$ stretch and $\tilde O(n)$ edges.

## Proof sketch

The ruling set algorithm repeatedly halves the identifier space bit by bit: in each step vertices whose current bit is $1$ are removed if they have a nearby surviving vertex with bit $0$, keeping distances among survivors large while ensuring domination grows by $O(1)$ per level; clustering via network decomposition compresses the $O(\log n)$ levels into $O(\log\log n)$ domination distance. Hitting sets and spanners derandomize sampling arguments whose analyses need only pairwise independence, using conditional expectations over clusters of a network decomposition.

## Depends on

- [Network decomposition with weak or strong diameter](network-decomposition-weak-strong-diameter.md)
- [The CONGEST model of distributed computing](the-congest-model.md)

## Proof depends on

- [Faster deterministic network decomposition in O(log^5 n) rounds](faster-deterministic-network-decomposition.md)

## Sources

- M. Ghaffari, C. Grunau, B. Haeupler, S. Ilchi, V. Rozhoň, "Improved Distributed Network Decomposition, Hitting Sets, and Spanners, via Derandomization", SODA 2023, arXiv:2209.11669.
- M. Ghaffari, C. Grunau, "Near-Optimal Deterministic Network Decomposition and Ruling Set, and Improved MIS", FOCS 2024, arXiv:2410.19516.
