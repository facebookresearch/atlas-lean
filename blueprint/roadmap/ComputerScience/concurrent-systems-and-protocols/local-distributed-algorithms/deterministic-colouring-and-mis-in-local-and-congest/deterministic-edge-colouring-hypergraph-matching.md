# Deterministic edge colouring via hypergraph maximal matching

Let $G = (V, E)$ be a simple connected graph with $n$ vertices and maximum degree $\Delta$, whose vertices carry distinct identifiers from $\{1, \dots, n^{O(1)}\}$. There is a deterministic LOCAL algorithm that computes a maximal matching in $n$-vertex hypergraphs of rank $r$ (each hyperedge has at most $r$ vertices) and maximum degree $\Delta$ in $O(r^2 \log(n\Delta) \log n \log^4 \Delta)$ rounds; an earlier algorithm based on rounding fractional matchings takes $O(r^5 \log^{6 + \log r} \Delta \cdot \log n)$ rounds. As a consequence, a $(2\Delta - 1)$-edge colouring of $G$ (indeed a list edge colouring with lists of size $\deg(e) + 1$, where $\deg(e)$ is the number of edges sharing an endpoint with $e$) can be computed deterministically in $\mathrm{poly}(\log n)$ rounds, already $O(\log^7 \Delta \cdot \log n)$ by the earlier algorithm, and so can a $(1 - \varepsilon)$-approximate maximum matching for constant $\varepsilon$.

## Proof sketch

The $O(r^2 \log(n\Delta) \log n \log^4 \Delta)$ bound (Ghaffari–Harris–Kuhn) derandomizes a randomized algorithm. Its core is hypergraph degree splitting: colouring hyperedges red or blue uniformly at random splits every vertex of degree at least $\delta = \Theta(\log(n\Delta)/\varepsilon^2)$ nearly evenly with high probability, and this choice is derandomized by the method of conditional expectations in the SLOCAL model and turned into a LOCAL algorithm on a hypergraph whose high-degree vertices are split into virtual vertices of degree $\Theta(\delta)$. Repeated splitting reduces the degrees while keeping them proportional, after which colouring the line graph of the sparse remaining hypergraph yields a matching covering an $\Omega(1/r)$ fraction of the vertices of degree at least $\Delta/2$; iterating halves the maximum degree. The earlier bound (Fischer–Ghaffari–Kuhn) instead rounds a fractional hypergraph matching of large weight deterministically, using defective colourings to sequentialize conflicting rounding decisions; that fractional-rounding argument gives only the $O(r^5 \log^{6 + \log r} \Delta \cdot \log n)$ bound. Edge colouring reduces to rank-$3$ hypergraph maximal matching: take $2\Delta - 1$ copies of $G$, add a vertex $w_e$ for each edge $e$ to all copies of $e$, and give $e$ colour $i$ when its $i$-th copy is matched.

## Depends on

- [The LOCAL model](../../distributed-execution-models/the-local-model.md)
- [Hypergraph](../../../../Combinatorics/extremal-set-theory/hypergraph-colouring-matching/erd-s-faber-lov-sz-conjecture/hypergraph.md)
- [Proper edge coloring](../../../../GraphTheory/graph-coloring/part-01/edge-coloring/is-proper-edge-coloring.md)

## Proof depends on

- [Network decompositions convert sequential local algorithms into LOCAL algorithms](../deterministic-network-decomposition/slocal-to-local-via-network-decomposition.md)

## Sources

- M. Fischer, M. Ghaffari, F. Kuhn, "Deterministic Distributed Edge-Coloring via Hypergraph Maximal Matching", FOCS 2017, arXiv:1704.02767, Theorems 1.1 and 1.4 and Lemma 1.3.
- M. Ghaffari, D. G. Harris, F. Kuhn, "On Derandomizing Local Distributed Algorithms", FOCS 2018, arXiv:1711.02194, Theorems 1.2 and 3.1 and Section 4.
