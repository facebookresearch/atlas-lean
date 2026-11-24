# Power Valid

Source-faithful validity of a power-labelled ordered merge tree.

`listBase` is the absolute base of the complete input, `listLength` is its
finite-width length, and `base` is the absolute base of this subtree.  The
recursive bases force the leaves to be contiguous and in source order.  At an
internal node, `power` is exactly the transcribed `powerloop` result for the
aggregate left and right spans.  The final two clauses are the strict
min-Cartesian heap condition for internal children; leaves carry no node
power.
