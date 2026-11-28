# Energy balance of the discretized Biot consolidation equations

Let `m` and `n` be finite index sets, for the displacement and the pressure coordinates. Let `K`
(`m × m`) and `C` (`n × n`) be symmetric real matrices, `Q` an `m × n` real matrix and `H` an
`n × n` real matrix. Let `u`, `f` (with values in `ℝ^m`) and `p`, `s` (with values in `ℝ^n`) be
functions of time, where every coordinate of `u` and of `p` has, at every time `t`, the derivative
`u'(t)` and `p'(t)` respectively, and suppose that at every time `K u - Q p = f` and
`C p' + Qᵀ u' + H p = s`.

Then at every time `t` the stored energy `E = (1 / 2) * (u · K u + p · C p)` has the derivative
`E'(t) = u'(t) · f(t) + p(t) · s(t) - p(t) · H p(t)`: the input power minus the dissipation. The
opposite signs of the two coupling terms `-Q p` and `+Qᵀ u'` are essential. The identity needs only
the symmetry of `K` and `C`; reading the quadratic forms as an energy and a dissipation uses the
positivity of the physical model (`K`, `C` and `H` positive semidefinite). Since `f = K u - Q p`,
the load has the derivative `f' = K u' - Q p'`; with the coupling matrix written as `-Q` and a
constant load rate `f' = df` and source `s`, the differentiated first equation and the second
equation are those of the [finite Biot rate system](satisfies-biot-rate-system.md), whose letters
`m` and `n` name the coordinate sets the other way round.
