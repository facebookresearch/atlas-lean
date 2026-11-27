# The linear plant's initial-value problem has a decaying solution

For every initial state `e₀ ∈ ℝ⁴` there is a function `e` from the reals to `ℝ⁴` with `e(0) = e₀`,
`e'(t) = A e(t)` at every real `t`, where `A e` is the
[reduced linear plant](linear-reduced-field.md), and

`‖e(t)‖ ≤ √8 exp(−t / 4) ‖e₀‖`

for every `t ≥ 0`, with `‖·‖` the Euclidean norm. By [uniqueness](exists-unique-linear-reduced-field-solut.md)
it is the only global solution.
