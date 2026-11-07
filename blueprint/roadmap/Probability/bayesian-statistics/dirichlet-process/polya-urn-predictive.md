# Blackwell–MacQueen urn predictive law

The predictive law in the **Blackwell–MacQueen urn**: after observations `x₀, …, x_{n-1}`,
the next observation has law `(α H + ∑ᵢ δ_{xᵢ}) / (α + n)`. It is a probability measure for
`α > 0` and a probability measure `H` (`isProbabilityMeasure_polyaUrnPredictive`); outside that
domain the definition is total but meaningless (e.g. `α = n = 0` gives the zero measure).
