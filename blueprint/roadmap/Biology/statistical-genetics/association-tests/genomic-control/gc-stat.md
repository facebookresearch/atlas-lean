# Genomic-control statistic with the estimated factor λ̂

For real scores `z_0, …, z_{m-1}` of `m` genes and a gene `j`, the genomic-control statistic of gene
`j` with the [mean-based estimate](lambda-hat.md) `λ̂ = (1 / m) ∑ₖ zₖ²` is

`T_j = z_j² / λ̂`,

the 1-df statistic of gene `j` divided by an estimate computed from all `m` genes, gene `j`
included. The intended domain is a score vector that is not identically zero, where `λ̂ > 0`. If all
scores vanish, `λ̂ = 0` and the convention `x / 0 = 0` gives `T_j = 0`.
