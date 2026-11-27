# Generator of a birth–death chain on a finite active population

For a natural number `N`, a real `α` and a function `f : ℕ → ℝ`, the birth–death generator is the
matrix `Q` on the states `0, 1, …, N` with `Q(i, i + 1) = (N - i) f(i)` (birth),
`Q(i, i - 1) = α i` (death), `Q(i, i) = -((N - i) f(i) + α i)`, and `Q(i, j) = 0` otherwise. There
is no entry above state `N` or below state `0`, so at the endpoints the diagonal keeps only the
remaining rate. It is a [rate matrix](birth-death-is-rate-matrix.md) when `α ≥ 0` and `f(i) ≥ 0` for
`i ≤ N`; in the model the activation `f` and the death rate `α` are nonnegative.
