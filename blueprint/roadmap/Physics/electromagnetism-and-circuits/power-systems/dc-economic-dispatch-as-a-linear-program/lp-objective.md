# Objective of the dispatch linear program

For cost coefficients `c`, the objective vector of the (maximized) linear program is `-c` on the
positive parts of the generation, `0` on the positive parts of the angles, `c` on the negative parts
of the generation and `0` on the negative parts of the angles. Its value at an LP point is minus the
[cost](dispatch-cost.md) of the decoded generation
([objective identity](lp-objective-dot-product.md)).
