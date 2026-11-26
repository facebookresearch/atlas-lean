# Node Count build

Storage bound: the tree built from a list of length `n` has exactly
`2 * n - 1` nodes. For `n = 0` both sides are `0` (`build []` is the empty
tree), and for `n = 1` the tree is one leaf. For `n ≥ 2` both halves of the
split are nonempty, and halves of lengths `a` and `b` give
`(2 * a - 1) + (2 * b - 1) + 1 = 2 * (a + b) - 1` nodes.
