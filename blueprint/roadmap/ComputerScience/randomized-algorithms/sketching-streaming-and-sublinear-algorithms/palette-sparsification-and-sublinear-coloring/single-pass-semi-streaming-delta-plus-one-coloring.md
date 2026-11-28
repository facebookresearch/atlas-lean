# Single-pass semi-streaming (Delta + 1)-coloring in dynamic graph streams

There is a randomized single-pass streaming algorithm that, given $n$ and $\Delta$ in advance and a dynamic graph stream of an $n$-vertex graph of maximum degree $\Delta$, uses $O(n\log^{c} n)$ bits for an absolute constant $c$ and polynomial time, and outputs a proper $(\Delta + 1)$-coloring with high probability. Analogous palette-sparsification arguments give an $O(1)$-round algorithm in the massively parallel computation model with $\widetilde{O}(n)$ memory per machine, and a one-round algorithm when the machines share public randomness.

## Proof sketch

Before the stream, sample the lists $L(v)$ of $O(\log n)$ colors, which fixes the color classes $\chi_c = \{v : c \in L(v)\}$ and, for every vertex $v$, the set $P_v$ of pairs joining $v$ to $\bigcup_{c \in L(v)} \chi_c$. For every $v$, run a linear-sketch sampler built from $L_0$ samplers that returns $k = O(\log^2 n)$ of the edges of the final graph inside $P_v$, or all of them if there are fewer, in $O(k\log^3 n)$ bits; it tolerates insertions and deletions. By the conflict-graph lemma every vertex has $O(\log^2 n)$ neighbors in the final conflict graph with high probability, so the conflict graph is recovered exactly, and the palette sparsification theorem guarantees that it has an $L$-coloring, which is a proper $(\Delta + 1)$-coloring of the input. To find this coloring in polynomial time, the algorithm also computes, in the same pass and $\widetilde{O}(n)$ space, an approximate sparse-dense decomposition from sampled vertex neighborhoods and sampled edges, and then follows the three coloring phases of the proof of the palette sparsification theorem.

## Depends on

- [Semi-streaming graph model with insertion-only, dynamic and random-order edge streams](../semi-streaming-matching-and-vertex-cover/semi-streaming-graph-model.md)
- [The massively parallel computation model](../../../parallel-algorithms/massively-parallel-computation-graph-algorithms/massively-parallel-computation-model.md)

## Proof depends on

- [Assadi-Chen-Khanna palette sparsification theorem for (Delta + 1)-coloring](palette-sparsification-theorem-delta-plus-one.md)
- [The conflict graph of palette sparsification has O(n log^2 n) edges](conflict-graph-has-quasilinear-size.md)
- [Jowhari-Sağlam-Tardos samplers: zero-relative-error L0 sampling in O(log^2 n) bits](../optimal-distinct-elements-and-lp-sampling/l0-sampler-with-log-squared-bits.md)
- [Sparse-dense decomposition of graphs of maximum degree Delta into sparse vertices and almost-cliques](sparse-dense-decomposition-of-bounded-degree-graphs.md)

## Sources

- Sepehr Assadi, Yu Chen, Sanjeev Khanna, "Sublinear Algorithms for (Delta + 1) Vertex Coloring", SODA (2019), arXiv:1807.08886.
