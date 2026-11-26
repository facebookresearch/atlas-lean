# Deterministic edge colouring via hypergraph maximal matching

Let $G = (V, E)$ be a simple connected graph with $n$ vertices and maximum degree $\Delta$, whose vertices carry distinct identifiers from $\{1, \dots, n^{O(1)}\}$. There is a deterministic LOCAL algorithm that computes a maximal matching in hypergraphs of rank $r$ (each hyperedge has at most $r$ vertices) and maximum degree $\Delta$ in $O(r^2 \log(n\Delta) \log n \log^4 \Delta)$ rounds. As a consequence, a $(2\Delta - 1)$-edge colouring of $G$ can be computed deterministically in $\mathrm{poly}(\log n)$ rounds, and so can a $(1 - \varepsilon)$-approximate maximum matching for constant $\varepsilon$.

## Proof sketch

Compute a fractional hypergraph matching of large weight by a deterministic rounding of a multiplicative-weights fractional solution, using a defective colouring to sequentialize conflicting rounding decisions; each rounding step loses only a $1 - 1/\mathrm{poly}(r)$ factor. Iterating extracts a constant fraction of a maximal matching per phase. Edge colouring reduces to hypergraph maximal matching on the hypergraph whose hyperedges are (edge, colour) choices with conflicts of rank $3$.

## Depends on

- [Locally checkable labeling problem](../lcl-problems-and-the-locality-landscape/locally-checkable-labeling-problem.md)

## Proof depends on

- [Network decompositions convert sequential local algorithms into LOCAL algorithms](../deterministic-network-decomposition/slocal-to-local-via-network-decomposition.md)

## Sources

- M. Fischer, M. Ghaffari, F. Kuhn, "Deterministic Distributed Edge-Coloring via Hypergraph Maximal Matching", FOCS 2017, arXiv:1704.02767.
- M. Ghaffari, D. G. Harris, F. Kuhn, "On Derandomizing Local Distributed Algorithms", FOCS 2018, arXiv:1711.02194.
