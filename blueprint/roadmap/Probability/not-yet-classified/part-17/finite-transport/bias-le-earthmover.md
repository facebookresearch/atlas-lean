# Score-gap bound by the earthmover value

Let `S` and `T` be probability
distributions on a finite type `V` (nonnegative entries summing to `1`) and `f : V → ℝ` a
score with `|f x - f y| ≤ d x y` for all `x, y`. Then the gap between the expectations of
`f` under `S` and under `T`, `bias S T f = |∑ x, S x * f x - ∑ x, T x * f x|`, is at most
`earthmover d S T`.
