# Paths solving the finite Biot consolidation rate system

For finite index sets, let `K` be an `n × n` stiffness matrix, `Q` an `n × m` coupling matrix,
`C` and `H` `m × m` storage-compliance and conductance matrices, `df` a constant load rate and `s`
a constant source. Displacement and pressure paths `u : ℝ → ℝⁿ` and `p : ℝ → ℝᵐ` satisfy the
finite Biot rate system when `u` and `p` are differentiable and, at every time `t`, the
equilibrium rate equation `K u'(t) + Q p'(t) = df` and the storage balance
`-Qᵀ u'(t) + C p'(t) = s - H p(t)` hold. This is the dissipative sign convention: with `Q = 0`,
`C = H = I` and `s = 0` the pressure decays, `p' = -p`. No nonsingularity of the matrices is
assumed.
