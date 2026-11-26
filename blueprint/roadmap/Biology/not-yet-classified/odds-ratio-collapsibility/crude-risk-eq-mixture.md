# Common-weight mixture identity under `X ⊥ Z`

**Common-weight mixture identity under `X ⊥ Z`** (Greenland, Robins and Pearl 1999, p. 38).
Let `p x y z ≥ 0` be a joint mass function of binary `X, Y, Z` with total mass `1`, with observed
independence `X ⊥ Z` (`P(X = x, Z = z) = P(X = x) P(Z = z)` for all `x, z`) and
`P(X = x, Z = z) > 0` for all `x, z`, and suppose the crude risk for `X = 0` is positive,
`P(Y = 1 | X = 0) > 0`. Then for each `x`,
`P(Y = 1 | X = x) = ∑_z P(Z = z) P(Y = 1 | X = x, Z = z)` (a common-weight mixture over `Z`), and
the risk ratio standardized to `P(Z)`,
`∑_z P(z) P(Y = 1 | 1, z) / ∑_z P(z) P(Y = 1 | 0, z)`, equals the crude risk ratio
`P(Y = 1 | X = 1) / P(Y = 1 | X = 0)` (an observed-data identity; causal exchangeability is not
assumed or implied). By the mixture identity both denominators equal `P(Y = 1 | X = 0)`, so
neither is zero.

## Sources

- Greenland, Robins and Pearl (1999), pp. 37–38.
