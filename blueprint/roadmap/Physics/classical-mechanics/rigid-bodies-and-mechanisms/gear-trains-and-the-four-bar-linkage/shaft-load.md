# External torque on a shaft of a gear train

For a gear train of `n` [meshes](mesh.md), `n ≥ 0`, port torques `a_k` and `b_k` as for
[lossless meshes](is-lossless.md), and a shaft `j ∈ {0, …, n}`, the shaft load is
`T_j = a_j + b_{j-1}`, where `a_j` is counted only when `j < n` (shaft `j` is upstream of mesh
`j`) and `b_{j-1}` only when `j ≥ 1` (shaft `j` is downstream of mesh `j - 1`). For massless rigid
shafts in equilibrium it is the external torque applied to shaft `j`, whose power into the train
is `T_j ω_j`.
