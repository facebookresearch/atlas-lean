# Balance Preserving Contraction

Ear-contraction hypothesis: for every finite set `K` with at least two cells and every
boundary dart `a` of `K`, there is a strictly smaller nonempty finite set `K'` with a boundary dart
`a'` of the same corner balance.

This hypothesis is false (`StatMech.Lattice.not_balancePreservingContraction`, proved in
`CornerBalanceUnprobedSite.lean`): by strong induction from single cells it would force corner
balance `-4` on every boundary orbit of every finite nonempty set, but the inner orbit around a
one-cell hole (the four neighbours of a site) has corner balance `+4`. It is kept only as the
subject of that refutation; no theorem assumes it.
