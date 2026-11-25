# Mixture identity without confounding

**Mixture identity without confounding** (Greenland, Robins and Pearl 1999, p. 38). Let
`p x y z ≥ 0` be a joint mass function of binary `X, Y, Z` with total mass `1`, with `X`
independent of `Z` (`P(X = x, Z = z) = P(X = x) P(Z = z)` for all `x, z`) and
`P(X = x, Z = z) > 0` for all `x, z`, and suppose the crude risk of the unexposed is positive,
`P(Y = 1 | X = 0) > 0`. Then for each `x`,
`P(Y = 1 | X = x) = ∑_z P(Z = z) P(Y = 1 | X = x, Z = z)`, and the risk ratio standardized to
the distribution of `Z`, `∑_z P(z) P(Y = 1 | 1, z) / ∑_z P(z) P(Y = 1 | 0, z)`, equals the crude
risk ratio `P(Y = 1 | X = 1) / P(Y = 1 | X = 0)`; by the mixture identity both denominators equal
`P(Y = 1 | X = 0)`, so neither is zero.

## Sources

- Greenland, Robins and Pearl (1999), pp. 37–38.
