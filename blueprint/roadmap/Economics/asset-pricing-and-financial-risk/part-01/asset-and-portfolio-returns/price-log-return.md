# Log return between two prices

The log return from an initial price `P₀` to a terminal price `P₁`, for real `P₀` and `P₁`, is
`log (P₁ / P₀)`, the log return of the gross return `P₁ / P₀`. It is a log return only for
`P₀ > 0` and `P₁ > 0`. With the conventions `x / 0 = 0`, `log 0 = 0` and `log x = log |x|`, it is
`0` when `P₀ = 0` or `P₁ = 0` (so a total loss `P₁ = 0` gets the value `0` of an unchanged price,
although its gross return `0` is meaningful), and `log |P₁ / P₀|` when the two prices have
opposite signs.
