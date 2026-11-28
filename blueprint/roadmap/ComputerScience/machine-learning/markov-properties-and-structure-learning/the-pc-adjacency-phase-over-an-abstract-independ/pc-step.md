# One step of the PC adjacency phase

One step of round `d` at the pair `p = (i, j)`, visited with `i < j`: if `i` and `j` are
still adjacent and some candidate of size `d` separates them, delete the edge in both
directions and record that candidate as the separating set of `(i, j)` and of `(j, i)`.
