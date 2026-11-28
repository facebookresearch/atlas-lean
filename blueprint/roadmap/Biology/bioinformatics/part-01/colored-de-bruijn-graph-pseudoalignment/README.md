# Colored de Bruijn graph pseudoalignment

Pseudoalignment assigns a sequencing read to the reference sequences compatible with it by looking up its $k$-mers in a colored de Bruijn graph, where each $k$-mer stores its color set (the references containing it), instead of computing base-level alignments. The assignment rule determines sensitivity to closely related references and robustness to sequencing errors, and the structure of the graph allows most color sets to be stored implicitly.

- [Hybrid pseudoalignment and key k-mers of a colored de Bruijn graph](hybrid-pseudoalignment-and-key-k-mers-of-a-colored-de-bruijn-graph.md)
