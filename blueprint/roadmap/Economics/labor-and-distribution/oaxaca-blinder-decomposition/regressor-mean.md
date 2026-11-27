# Average regressor vector

The average regressor vector of an `n × κ` regressor matrix `X` is the vector of its column means:
its component `j` is `(1 / n) * ∑_i X(i, j)`. For `n = 0` the convention `x / 0 = 0` makes every
component `0`; the intended domain is `n ≥ 1`.
