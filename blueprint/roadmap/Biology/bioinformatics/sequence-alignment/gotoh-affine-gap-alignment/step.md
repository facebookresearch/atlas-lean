# Gotoh cell recurrence from diagonal, upper and left cells

The cell of `(a :: xs, b :: ys)` from the cells `diag` of `(xs, ys)`, `up` of `(xs, b :: ys)`
and `left` of `(a :: xs, ys)`: a match continues from `M`, a gap in `ys` from `X` (extending if
the previous column was one), a gap in `xs` from `Y`.
