# Estimated-factor statistics of random scores

Let `Z_0, …, Z_{m-1}` be real functions (random scores of `m` genes) on a sample space `Ω`. The
corrected statistic of gene `j` is the function

`T_j(ω) = Z_j(ω)² / λ̂(ω)`, where `λ̂(ω) = (1 / m) ∑ₖ Z_k(ω)²`,

the [estimated-factor statistic](gc-stat.md) of the score vector `(Z_0(ω), …, Z_{m-1}(ω))`: `λ̂` is
computed at the same sample point from all genes, gene `j` included. At a sample point where all
scores vanish, `T_j(ω) = 0` by the convention `x / 0 = 0`.
