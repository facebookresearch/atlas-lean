# With symmetric M, K, A, the energy balance at every time of a solution

Let `n` and `m` be finite index sets, `M`, `K`, `C` constant real `n × n` matrices, `A`, `H`
constant real `m × m` matrices and `G` a constant real `n × m` matrix, with `M`, `K` and `A`
symmetric. Let `x`, `v`, `dv` be functions of time with values in real vectors indexed by `n`, and
`p`, `dp` functions of time with values in real vectors indexed by `m`. Suppose that at every real
time `s` each component of `x` has derivative the matching component of `v(s)`, each component of
`v` has derivative that of `dv(s)`, each component of `p` has derivative that of `dp(s)`, and
`M dv(s) + C v(s) + K x(s) - G p(s) = 0` and `A dp(s) + H p(s) + Gᵀ v(s) = 0`. Then at every time
`t` the quadratic form `E = ½ (vᵀ M v + xᵀ K x + pᵀ A p)` has derivative
`-(v(t)ᵀ C v(t) + p(t)ᵀ H p(t))`, by the [balance at one time](vibroacoustic-port-energy.md).
Reading `E` as stored energy and `vᵀ C v + pᵀ H p` as dissipated power uses positive
semidefinite `M`, `K`, `A`, `C` and `H`, which the identity does not assume.
