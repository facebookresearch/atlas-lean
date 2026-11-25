# Spring stiffness with positive masses has nonnegative mode eigenvalues

Let `ι` be a finite set of nodes with pair weights `k` satisfying `k_{ij} = k_{ji}`, `k_{ii} = 0`
and `k_{ij} ≥ 0`, wall stiffnesses `w_i ≥ 0`, and masses `m_i > 0`. If a nonzero `v : ι → ℝ` and a
real `λ` satisfy `K v = λ (m ⊙ v)`, with `K` the [stiffness matrix](stiffness-matrix.md) and
`(m ⊙ v)_i = m_i v_i`, then `λ ≥ 0`. The spring structure matters: for a general symmetric matrix
with a negative eigenvalue, the generalized eigenvalue problem with positive masses has a negative
eigenvalue.
