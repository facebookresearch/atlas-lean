# Reduction wins

The core of the reduction: if the Merkle forger wins with keys
`Function.update skO j skStar` and coins `r`, using the honest Lamport key at index `j`, then the
reduction with coins `(j, skO, r)` forges a Lamport signature under `skStar`.
