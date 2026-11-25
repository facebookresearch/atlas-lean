# Heterogeneous Bruhat Decomposition Aux

Direct structural recursion on `card m` for the canonical decomposition.

This refactors the former `strongRecOn` into plain `Nat.rec` with a reusable
private nonzero-branch equation `heterogeneousBruhatDecompositionAux_build`.
The zero case is `emptyDecompositionOfCardZero`. The successor case extracts
the canonical column/row, clears, recurses on the deleted pivot, and
reassembles via `heterogeneousBruhatDecompositionAux_build`. This gives
stable unfolding for the coefficient-naturality proof.
