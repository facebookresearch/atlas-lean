# Bootstrapped discount factors are unique

Let `C` be an `n × n` real cash-flow matrix, `C_{ij}` the payment of bond `i` at date `j`, that
is lower triangular (`C_{ij} = 0` for `j > i`: bond `i` pays only at dates up to its maturity
`i`) and has nonzero diagonal entries `C_{ii} ≠ 0`. If two vectors of discount factors `D` and
`D′` give the same bond prices, `C D = C D′`, then `D = D′`. No positivity of the discount
factors is claimed.
