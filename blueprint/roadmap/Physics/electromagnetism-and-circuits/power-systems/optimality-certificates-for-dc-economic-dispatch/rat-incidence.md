# Rational incidence matrix of a network

For finitely many buses and branches, each branch with a tail and a head bus, the rational incidence
matrix has entry `[v = tail(e)] - [v = head(e)]` at bus `v` and branch `e` (`1` at the tail, `-1` at
the head, `0` for a loop). The rational objects copy the real ones entrywise, so that the checker is
computable; the [casting lemmas](rat-lp-matrix-map.md) identify them with the real linear program.
