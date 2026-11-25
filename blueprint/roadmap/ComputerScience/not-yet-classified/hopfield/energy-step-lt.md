# Energy descent at zero threshold

**Energy descent at zero threshold** (Hopfield 1982, Eq. [7]–[8]). Let `T` be a symmetric weight
matrix (`Matrix.IsSymm T`). Then for every neuron `i` and state `v`, if the zero-threshold update of
neuron `i` changes the state (`step T 0 i v ≠ v`), it strictly decreases the energy:
`energy T (step T 0 i v) < energy T v`.
