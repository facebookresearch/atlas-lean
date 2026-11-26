# Reduced pressure-rate equation of the Biot system

For finite index sets, let `K` be invertible with inverse `Kinv` (`K Kinv = Kinv K = I`). If
paths `u`, `p` satisfy the finite Biot rate system `K u' + Q p' = df`,
`-Qᵀ u' + C p' = s - H p` (with `u`, `p` differentiable), then at every time `t` the pressure
rate solves the reduced storage equation `S p'(t) = Qᵀ Kinv df + s - H p(t)`, where
`S = Qᵀ Kinv Q + C`, and the displacement rate is recovered as `u'(t) = Kinv (df - Q p'(t))`.
