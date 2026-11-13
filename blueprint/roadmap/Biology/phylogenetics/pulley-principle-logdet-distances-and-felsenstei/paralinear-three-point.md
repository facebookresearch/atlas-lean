# Additivity of the LogDet distance at a separating vertex

**Additivity of the LogDet distance at a separating vertex** (Steel 1994; Lockhart et al.
1994; Lake 1994). Let `Y` have distribution `p` (positive) and let `X` and `Z` be conditionally
independent given `Y`, with transition matrices `M` (from `Y` to `X`) and `N` (from `Y` to `Z`)
whose rows sum to `1` and whose determinants are nonzero. The joint distribution matrices are
`F_XY = Mᵀ Π_Y`, `F_YZ = Π_Y N` and `F_XZ = Mᵀ Π_Y N`, and `d(X, Z) = d(X, Y) + d(Y, Z)`. The
identity uses no sign condition on `M` and `N`; with nonnegative entries all logarithms are of
positive numbers (`vecMul_pos`).
