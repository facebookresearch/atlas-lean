# Register allocation

Assigning machine registers to the temporaries of a program. Graph-coloring allocation colors an interference graph built from [live-variables analysis](../static-analysis/live-variables-analysis.md); deciding colorability with $k$ registers is NP-complete for general programs, so allocators simplify low-degree nodes and coalesce moves conservatively. For programs in strict SSA form the interference graph is chordal and the dominance order gives an optimal coloring, while after classical SSA elimination the problem is NP-complete again. Linear-scan allocation works on live intervals. That coloring preserves semantics is [stated separately](../compiler-correctness/register-allocation-by-graph-coloring-preserves.md).

- [Interference graphs](interference-graphs.md)
- [Register allocation is NP-complete](register-allocation-is-np-complete.md)
- [Removing a low-degree node preserves colorability](removing-a-low-degree-node-preserves-colorability.md)
- [Briggs's conservative coalescing](briggs-s-conservative-coalescing.md)
- [Interfering variables of a strict SSA program are simultaneously live](cliques-in-ssa-interference-graphs.md)
- [Dominance order gives a perfect elimination order](dominance-order-gives-a-perfect-elimination-order.md)
- [Optimal coloring of SSA interference graphs](optimal-coloring-of-ssa-interference-graphs.md)
- [Register allocation after classical SSA elimination is NP-complete](register-allocation-after-classical-ssa-eliminati.md)
- [Linear-scan register allocation](linear-scan-register-allocation.md)
