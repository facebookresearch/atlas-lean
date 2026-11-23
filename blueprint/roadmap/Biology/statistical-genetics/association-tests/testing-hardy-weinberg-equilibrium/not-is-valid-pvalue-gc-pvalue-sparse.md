# Genomic control is not a universal repair

In the sparse HWE null model (`N = 10`,
`n_A = 2`) the chi-square statistic takes only the two values `10` and `10/81`, and for every
inflation factor `lam > 0` the genomic-control p-value is still not valid: at the level
`t = gcPValue lam (10/81)`, its own larger value (about `0.72` at `lam = 1`, tending to `1` as
`lam` grows), it rejects with probability one. This failure comes from the discreteness of the
null law, not from genomic control specifically. At the usual level `0.05` the failure is proved
only for `lam ∈ (0, 1]` (`gcPValue_sparse_rejection_ge`); that range includes values below the
clipping floor, so see that theorem for the correct interpretation.
