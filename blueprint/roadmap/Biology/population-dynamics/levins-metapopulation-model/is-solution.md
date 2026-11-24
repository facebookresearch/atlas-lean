# Forward solution of the Levins equation with immigration

For real `c`, `e` and `m`, a function `p : ℝ → ℝ` solves the Levins equation with immigration for
`t ≥ 0` if at every `t ≥ 0` it has derivative
`p'(t) = f(p(t)) = c p(t) (1 - p(t)) - e p(t) + m (1 - p(t))`, where `f` is the
[balance](balance.md).

The derivative at `t = 0` is the two-sided one. Nothing is required at negative times, and no
initial value or range of `p` is imposed.
