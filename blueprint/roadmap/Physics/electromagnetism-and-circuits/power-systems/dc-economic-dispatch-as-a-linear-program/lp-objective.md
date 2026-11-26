# Objective of the dispatch linear program

For cost coefficients `c`, the objective vector of the (maximized) linear program is `-c` on the
generation entries of the first nonnegative coordinate block, `0` on its angle entries, `c` on the
generation entries of the second block and `0` on its angle entries. Its value at an LP point is
minus the [cost](dispatch-cost.md) of the decoded generation
([objective identity](lp-objective-dot-product.md)).
