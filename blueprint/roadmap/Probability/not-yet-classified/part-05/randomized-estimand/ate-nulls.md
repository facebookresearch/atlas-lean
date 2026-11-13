# Ate Nulls

The **true causal nulls**: the endpoints `j` whose average treatment effect
`E[Y₁ j - Y₀ j]` is zero and whose contrast `Y₁ j - Y₀ j` is integrable. The integrability
part is essential: a Bochner integral is `0` when the integrand is not integrable, so an
endpoint with an undefined ATE must not be classified as a true causal null.
