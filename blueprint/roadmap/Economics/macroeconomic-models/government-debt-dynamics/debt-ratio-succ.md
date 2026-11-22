# Debt-ratio recurrence

Let output be nonzero, `Y(t) ≠ 0` for every `t`, and grow as
`Y(t + 1) = (1 + g) * Y(t)` with `1 + g ≠ 0`, and let nominal debt follow
`B(t + 1) = (1 + r) * B(t) + D(t + 1)`. Then the debt ratio `b(t) = B(t) / Y(t)`
satisfies

`b(t + 1) = ((1 + r) / (1 + g)) * b(t) + d(t + 1)`,

where `d(t + 1) = D(t + 1) / Y(t + 1)` is the primary-deficit ratio against the
output of the same period.
