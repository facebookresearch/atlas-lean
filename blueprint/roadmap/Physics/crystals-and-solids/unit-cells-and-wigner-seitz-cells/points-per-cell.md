# Number of lattice points per conventional cell

Let two [Bravais lattices](../bravais-lattices/bravais-lattice.md) have basis matrices `B_c` and
`B_f` and lattices `L_c` and `L_f`. The number of points of `L_f` per cell of `L_c` is the index of
`L_c ∩ L_f` in `L_f`, the number of elements of the quotient group `L_f / (L_c ∩ L_f)`. When `L_c`
is a [sublattice](is-sublattice-of.md) of `L_f` it is the index of `L_c` in `L_f`, a positive
integer equal to `|det B_c| / |det B_f|` ([volume ratio](points-per-cell-eq-volume-ratio.md)). When
the index is infinite, which can happen without the sublattice hypothesis, the value is `0`, by the
convention that an infinite set has natural-number cardinality `0`.

It is not the number of points of `L_f` in the closed [conventional cell](conventional-cell.md) of
`L_c`, whose boundary points are shared with neighbouring cells.
