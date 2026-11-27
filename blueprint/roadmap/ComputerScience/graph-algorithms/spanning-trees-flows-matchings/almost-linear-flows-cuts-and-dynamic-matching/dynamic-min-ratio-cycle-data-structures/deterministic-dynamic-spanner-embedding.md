# Deterministic dynamic spanners with low-recourse short embeddings under deletions and vertex splits

Let $G$ be an $m$-edge, $n$-vertex unweighted undirected dynamic graph undergoing batches $U^{(1)}, U^{(2)}, \ldots$ of edge deletions and $\widetilde{O}(n)$ vertex splits in total, with maximum degree $\Delta_{\max}(G)$. There is a deterministic algorithm that maintains a spanner $H^{(t)} \subseteq G^{(t)}$ and an embedding $\Pi_{G \to H}$ such that, for $\gamma_s = \exp(O(\log^{8/9} m\log\log m))$:

1. $H^{(t)}$ has $\widetilde{O}(n\gamma_s)$ edges and the amortized number of edge changes to $H$ per update in $U^{(t)}$ is $O(\gamma_s)$;
2. every embedding path has at most $\gamma_s$ edges and every vertex of $H$ lies on embedding paths of total multiplicity $O(\gamma_s\Delta_{\max}(G))$;
3. after each batch it reports a set $D^{(t)}$ of spanner edges, of amortized size $O(\gamma_s)$ per update, outside which no embedding path gained an edge;
4. initialization takes $\widetilde{O}(m\gamma_s)$ time and the amortized time per update is $O(\gamma_s\Delta_{\max}(G))$ times its encoding size.

A randomized analogue with slightly better parameters underlies the original almost-linear time min-cost flow data structure.

## Proof sketch

The static core is a deterministic sparsifier: decompose the graph into $\phi$-expanders with $\phi = \exp(-O(\log^{2/3} m))$, replace each expander by a constant-degree expander on its vertices whose edges are routed by short paths, and re-embed through deterministic expander pruning and path queries. A dynamic hierarchy of $L = \log^{1/9} m$ levels with geometrically sized batches rebuilds level $i$ after $n^{i/L}$ updates, so recourse per update is $n^{1/L}$ times the per-level loss. Taking $L = \log^{1/9} m$ balances $n^{1/L}$ against $(\gamma_c\gamma_\ell)^{O(L^2)}$, giving $\gamma_s$.

## Depends on

- [Sparsified core graphs with short low-congestion embeddings](sparsified-core-graph-embedding.md)
- [Dynamic graph problems](../../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/dynamic-graph-problems.md)
- [Amortized cost of an operation](../../../../data-structures/amortized-analysis/amortized-cost.md)

## Proof depends on

- [C-expander](../../../../../GraphTheory/graph-families-and-operations/expander-graphs/is-cexpander.md)

## Sources

- Jan van den Brand, Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, Aaron Sidford, "A Deterministic Almost-Linear Time Algorithm for Minimum-Cost Flow", FOCS (2023), arXiv:2309.16629.
- Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, "Maximum Flow and Minimum-Cost Flow in Almost-Linear Time", FOCS (2022), arXiv:2203.00671.
