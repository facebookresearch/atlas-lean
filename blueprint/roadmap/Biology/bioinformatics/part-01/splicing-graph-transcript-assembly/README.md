# Splicing-graph transcript assembly

RNA-seq reads from one gene can be summarized as a splicing graph: a directed acyclic graph whose nodes are maximal unbranched exonic segments and whose edges are observed splice junctions weighted by read depth. Transcript isoforms are then recovered as a set of source-to-sink paths that covers every edge and whose per-isoform abundances explain the junction depths.

- [Coverage bin packing on a topologically ordered splicing graph](coverage-bin-packing-on-a-topologically-ordered-splicing-graph.md)
