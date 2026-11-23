# The burden score ignores the weight of a variant with no carriers

Let `X` be a real `n × q` covariate matrix, `V` a real `n × n` matrix, `G` a real `n × m` genotype
matrix and `a ∈ ℝᵐ` variant weights. If variant `j` has no carriers, that is, its column of `G` is
zero (`Gᵢⱼ = 0` for every individual `i`), then replacing its weight `aⱼ` by any real number `c`
leaves the [burden score](burden-score.md) `B(y)` unchanged for every phenotype `y ∈ ℝⁿ`: the
collapsed genotype `C = G a` does not change. No condition on `X` or `V` is needed.
