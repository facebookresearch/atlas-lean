# Merge Lo Gallop Round equation

The complete `merge_lo` gallop round, stated as a public equation.  In
particular, the first search is `gallop_right(activeA, firstB, na, 0)` and its
insertion index is the number of A entries copied; the second is
`gallop_left(data, firstA, nb, 0)` and its insertion index is the number of B
entries moved.
