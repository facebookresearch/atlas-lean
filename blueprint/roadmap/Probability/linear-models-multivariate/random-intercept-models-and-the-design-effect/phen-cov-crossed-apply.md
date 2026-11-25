# Entries of Z G Zᵀ + σ_e² I for crossed random intercepts

For finite index types `I` and `J` and real numbers `σ_s²`, `σ_w²` and `σ_e²`, let `Z` be the
[crossed design](crossed-design.md), `G` the [crossed random-effects covariance](crossed-cov.md) and
`σ_e² I` the residual covariance. The matrix `V = Z G Zᵀ + σ_e² I` has entries
`V_{(i,j),(i',j')} = [i = i'] σ_s² + [j = j'] σ_w² + [(i, j) = (i', j')] σ_e²`, where `[·]` is `1`
if the condition holds and `0` otherwise: two observations share `σ_s²` if they have the same row
and `σ_w²` if they have the same column, and `σ_e²` appears only on the diagonal. The identity is
algebraic and holds for all real components; under the
[Gaussian crossed model](covariance-crossed-response.md) with nonnegative components, `V` is the
covariance matrix of the response.
