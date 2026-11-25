# Design matrix of crossed random intercepts

For index types `I` (rows, for example participants or sires) and `J` (columns, for example items or
dams), the crossed design is the matrix `Z` with rows indexed by the pairs `(i, j) ∈ I × J` and
columns indexed by the disjoint union `I ⊔ J`: the row of observation `(i, j)` has entry `1` in
column `i` of `I` and in column `j` of `J`, and `0` elsewhere. Thus `Z = [S | W]` with `S` and `W`
the indicator matrices of the row and column factors, and observation `(i, j)` loads on the row
effect `i` and on the column effect `j`. Together with the
[diagonal random-effects covariance](crossed-cov.md) and a residual covariance `σ_e² I`, it gives
the [covariance of the crossed model](phen-cov-crossed-apply.md).
