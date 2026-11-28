# Single-variant score statistics

For a real `n × q` covariate matrix `X`, a real `n × n` matrix `V`, a real `n × m` genotype matrix
`G` and a phenotype `y ∈ ℝⁿ`, the score of variant `j` is

`Sⱼ = gⱼᵀ P y`,

where `gⱼ` is the genotype column of variant `j` and `P` the [null projection](proj-p.md) built from
`X` and `V`; in vector form `S = Gᵀ P y`.
