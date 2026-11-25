# Action of the support reaction matrix

For reaction components `s` acting at joints `sj_s` along directions `sd_s`, a finite set of
reaction components and a vector `ρ` of signed reaction coefficients, the
[reaction matrix](reaction-matrix.md) `R_sup` satisfies
`(R_sup ρ)(j, k) = ∑_{s : sj_s = j} ρ_s * (sd_s)_k` at every joint `j` and coordinate `k ∈ {0, 1}`:
the sum of the reaction forces acting at joint `j`.
