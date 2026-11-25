# Support reaction matrix of a planar truss

Let `J` (joints) and `R` (reaction components) be sets, where reaction component `s` acts at joint
`sj_s` along the direction `sd_s`, a vector of the plane. The reaction matrix has rows indexed by
the joint coordinates `(j, k)`, `k ∈ {0, 1}`, and columns by `R`: its entry in row `(j, k)` and
column `s` is `(sd_s)_k` if `sj_s = j` and `0` otherwise. Column `s` is thus the direction `sd_s`
placed at joint `sj_s`.
