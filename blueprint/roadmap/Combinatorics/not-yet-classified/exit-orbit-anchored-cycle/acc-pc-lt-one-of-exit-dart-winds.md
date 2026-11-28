# Peierls bound for bond percolation on `ℤ²`

**Peierls bound for bond percolation on `ℤ²`**, conditional form: `p_c(ℤ²) < 1`, assuming that
for every configuration with finite origin cluster the face loop of the exit orbit is a cycle
winding around the origin (`acc_ExitDartWinds`).

The literature result is unconditional (Peierls 1936; `p_c(ℤ²) = 1/2` by Kesten 1980). Here the
geometric input `acc_ExitDartWinds` is a hypothesis; it is not proved for general configurations.
See also `StatMech.Lattice.pc_lt_one_via_canonicalContour`, which assumes the weaker
`AnchoredCycleExists`.
