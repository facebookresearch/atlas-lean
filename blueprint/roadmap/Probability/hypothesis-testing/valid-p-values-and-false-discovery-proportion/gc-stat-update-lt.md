# Raising another gene's statistic lowers Tⱼ when zⱼ ≠ 0

Let `z_0, …, z_{m-1}` be real scores, `j` a gene with `z_j ≠ 0` and `k ≠ j` another gene. Replacing
`z_k` by any real `t` with `t² > z_k²` strictly lowers the [estimated-factor statistic](gc-stat.md)
of gene `j`: `T_j` computed from the modified scores is strictly smaller than `T_j` computed from
`z`. A strong non-null signal at gene `k` thus inflates `λ̂` and makes the test of every other gene
with a nonzero score strictly more conservative; a gene with zero score keeps `T_j = 0`.
