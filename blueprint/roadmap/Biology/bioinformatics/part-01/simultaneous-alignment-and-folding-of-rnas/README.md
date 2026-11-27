# Simultaneous alignment and folding of RNAs

Non-coding RNAs with low sequence identity are aligned reliably only by optimizing the alignment and the secondary structures of both sequences together, as in Sankoff's algorithm. Its $O(n^6)$ time is prohibitive, so practical variants restrict the search space using base-pair probabilities from the single-sequence structure ensembles. Strong enough ensemble-based sparsification brings the cost down to that of plain sequence alignment.

- [Ensemble-sparsified Sankoff alignment in quadratic time](ensemble-sparsified-sankoff-alignment-in-quadratic-time.md)
