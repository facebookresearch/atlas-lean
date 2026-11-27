# Single-pass semi-streaming (Delta + 1)-coloring in dynamic graph streams

There is a randomized single-pass streaming algorithm that, given $n$ and $\Delta$ in advance and a dynamic graph stream of an $n$-vertex graph of maximum degree $\Delta$, uses $O(n\log^{c} n)$ bits for an absolute constant $c$ and outputs a proper $(\Delta + 1)$-coloring with high probability. Post-processing at the end of the stream is not counted. Analogous palette-sparsification arguments give an $O(1)$-round algorithm in the massively parallel computation model with $\widetilde{O}(n)$ memory per machine.

## Proof sketch

Before the stream, sample the lists $L(v)$ of $O(\log n)$ colors, using $O(n\log^2 n)$ bits. The set of candidate conflict pairs is then fixed, and the algorithm maintains a linear $s$-sparse recovery sketch of the edge-indicator vector restricted to these pairs with $s = O(n\log^2 n)$, which tolerates insertions and deletions. By the conflict-graph lemma the final conflict graph has at most $s$ edges with high probability, so it is recovered exactly, and the palette sparsification theorem guarantees that it has an $L$-coloring, which is a proper $(\Delta + 1)$-coloring of the input.

## Depends on

- [Semi-streaming graph model with insertion-only, dynamic and random-order edge streams](../semi-streaming-matching-and-vertex-cover/semi-streaming-graph-model.md)
- [The massively parallel computation model](../../../parallel-algorithms/massively-parallel-computation-graph-algorithms/massively-parallel-computation-model.md)

## Proof depends on

- [Assadi-Chen-Khanna palette sparsification theorem for (Delta + 1)-coloring](palette-sparsification-theorem-delta-plus-one.md)
- [The conflict graph of palette sparsification has O(n log^2 n) edges](conflict-graph-has-quasilinear-size.md)
- [Exact 1-sparse recovery and detection with three linear counters](../optimal-distinct-elements-and-lp-sampling/one-sparse-recovery-by-fingerprints.md)

## Sources

- Sepehr Assadi, Yu Chen, Sanjeev Khanna, "Sublinear Algorithms for (Delta + 1) Vertex Coloring", SODA (2019), arXiv:1807.08886.
