# Scaling the GLS residual by the inverse covariance gives P y

For every real `n × q` covariate matrix `X`, every real `n × n` matrix `V` and every `y ∈ ℝⁿ`,

`V⁻¹ (y - X α̂) = P y`,

where `y - X α̂` is the [null-model GLS residual](gls-residual.md) and `P` the
[null projection](proj-p.md). No invertibility is assumed.
