# Fair classifiers are close outcome by outcome

For a classifier `M` on a finite
outcome set that is individually fair with respect to a task metric `d` (every row a
probability distribution and `tvDist (M x) (M y) ≤ d x y`), the probabilities of each
outcome `o` satisfy `|M x o - M y o| ≤ d x y`.
