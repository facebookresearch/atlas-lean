# Merge Lo Semantic Machine Invariant

Functional invariant of every live `merge_lo` machine.

The decomposition is deliberately stated against immutable whole-entry lists.
It therefore pins key/payload pairing as well as sortedness and stability.
`lastStrict` is the correctness form of the trimmed right-end sentinel used by
the `na = 1` tail.
