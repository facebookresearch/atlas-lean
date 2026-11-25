# Last Row Generator comm corr Prod Col

Last-row generator `x n j b` commutes with `corrProdCol i a L` when `j < n` and `j ≠ i`.
Orientation: `x (R := R) n j b * corrProdCol (R := R) i a L =
corrProdCol (R := R) i a L * x (R := R) n j b`.
Hypotheses `hj : j < n` and `hij : j ≠ i` are required. This is a commutation equality
only—not normality, membership, collection, landing, kernel, or Matsumoto.
Generic over `[Ring R]` and characteristic-two safe.
