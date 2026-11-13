# Binary loadings of a drift model

The model has binary loadings if every lineage weight is `0` or `1`.

Every tree model has binary loadings: there `weight X e` is the indicator of `e` lying on the
root-to-`X` path. The converse fails, since nothing forces the weight-`1` edge sets to be
compatible root-to-leaf paths: two edges of length `1` and four populations with weight
vectors `00`, `10`, `01`, `11` have binary loadings, but their `f2` distances form a square,
which violates the four-point condition of tree metrics. The results below use only the binary
values, so they apply to every tree.
