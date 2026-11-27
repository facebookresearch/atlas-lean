# Generic discrete-logarithm success count, fixed encoding

Let `q` be prime, let `enc` be
an encoding (a permutation of `ZMod q`), and let `A` be a decision tree on three labels with leaves
in `ZMod q` that makes at most `m` group operations on every path (`GTree.numQueries A ≤ m`). Run
on the labels `enc 0`, `enc 1` and `enc x` with the oracle `oracleOf enc`, `A` outputs `x` for at
most `(m + 3).choose 2 + 1` secrets `x ∈ ZMod q`.

## Sources

- V. Shoup, *Lower Bounds for Discrete Logarithms and Related Problems*, revised version of the Eurocrypt 1997 paper, Section 2, proof of Theorem 1.
