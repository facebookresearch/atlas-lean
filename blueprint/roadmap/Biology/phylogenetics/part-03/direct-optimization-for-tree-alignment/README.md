# Direct optimization for tree alignment

Heuristics for the tree alignment problem: given a tree whose leaves carry unaligned sequences, assign sequences to the internal vertices so that the sum of edit distances along edges is minimum (NP-hard). Direct optimization propagates compact sets of candidate ancestral sequences, encoded as strings over the power-set alphabet, in a post-order pass, and every cost it reports is achieved by an actual assignment.

- [Feasibility of direct optimization tree costs](feasibility-of-direct-optimization-tree-costs.md)
