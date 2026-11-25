# With symmetric M, K, A, the energy balance of the coupled system at t

Let `n` and `m` be finite index sets, for the structural and the acoustic coordinates. Let `M`,
`K`, `C` be constant real `n × n` matrices, `A`, `H` constant real `m × m` matrices and `G` a
constant real `n × m` matrix, with `M`, `K` and `A` symmetric (`C`, `H` and `G` need not be). Let
`x`, `v`, `dv` be functions of time with values in real vectors indexed by `n`, and `p`, `dp`
functions of time with values in real vectors indexed by `m`, and fix a time `t`. Suppose that at
`t` each component of the displacement `x` has derivative the matching component of `v(t)`, each
component of the velocity `v` has derivative that of `dv(t)`, each component of the pressure `p`
has derivative that of `dp(t)`, and the coupled equations hold at `t`:
`M dv(t) + C v(t) + K x(t) - G p(t) = 0` and `A dp(t) + H p(t) + Gᵀ v(t) = 0`. Then
`E(τ) = ½ (v(τ)ᵀ M v(τ) + x(τ)ᵀ K x(τ) + p(τ)ᵀ A p(τ))` has derivative
`-(v(t)ᵀ C v(t) + p(t)ᵀ H p(t))` at `τ = t`: the coupling power `v(t)ᵀ G p(t)` of the structural
equation cancels the term `p(t)ᵀ Gᵀ v(t)` of the acoustic one. Reading `E` as stored energy and
`vᵀ C v + pᵀ H p` as dissipated power uses positive semidefinite `M`, `K`, `A`, `C` and `H`, which
the identity does not assume.
