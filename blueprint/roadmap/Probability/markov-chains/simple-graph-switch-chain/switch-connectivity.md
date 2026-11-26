# Switch connectivity for a prescribed labelled degree sequence

For $n\ge4$, take a function $d:[n]\to\{0,\ldots,n-1\}$ with at least one simple undirected labelled realization. The state space $\mathcal G_d$ consists of all those realizations. A valid switch chooses four distinct vertices and replaces one perfect matching on them by a different one: both removed edges must be present and both added edges absent. Every pair of states is joined by a finite sequence of valid switches, allowing the empty sequence.

**Conventions.** Use a simple graph on a fixed finite vertex set, vertex degree, and replacement of the two edges of a perfect matching on four labels. Each valid replacement preserves the degree at every vertex.

## Depends on

- [The lazy switch chain on labelled degree realizations](degree-sequence-switch-kernel.md)

## Proof outline

A decomposition of the two-colored symmetric difference of equal-degree realizations into alternating closed trails, and a switch reduction that deals with chords already present in the graph.

Prove degree preservation and reversibility of the move, then the alternating-trail reduction with simple-graph legality at each intermediate step. A path may not pass through a multigraph or through a graph with a different degree sequence.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SwitchChain.lean#L163-L166)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/131.md)
- [Accompanying manuscript: Polynomial mixing of the switch chain for every graphical degree sequence](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Polynomial-Mixing-of-the-Switch-Chain-for-Every-Graphical-Degree-Sequence-September-25-2026/main.pdf)
- [Background: Cooper, Dyer and Greenhill, *Sampling regular graphs and a peer-to-peer network*, Combinatorics, Probability and Computing 16 (2007), 557–593](https://doi.org/10.1017/S0963548306007978)
