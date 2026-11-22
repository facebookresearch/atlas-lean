# Inverse Prediction

Inverse prediction from a fitted line (CH24.4): given fitted intercept `a`, fitted slope
`b` and a new response `y₀`, the predicted concentration is `x₀ = (y₀ - a) / b`. No Mathlib
or ATLAS definition covers fitted-line inverse prediction (`EarthScience` treats a known
line with the fitted case explicitly out of scope).
