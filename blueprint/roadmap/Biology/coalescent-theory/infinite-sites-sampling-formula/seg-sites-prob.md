# Tavaré's formula for the number of segregating sites

For a real number `θ` and natural numbers `n` and `m`, let

`p_{θ,n}(m) = (n - 1) ∑_{j=0}^{n-2} (-1)^j C(n - 2, j) θ^m / (θ + j + 1)^{m+1}`.

For `n ≥ 2` and `θ ≥ 0` it is the probability that a sample of `n` genes has `m` segregating
sites under the infinite-sites model with scaled mutation rate `θ`
([infinite-sites sampling formula](measure-real-seg-sites-eq-of-mutation.md)). It is defined for
all inputs: for `n ≤ 1` the sum is empty and the value is `0`; `θ^0 = 1`, also for `θ = 0`; and
a term whose denominator vanishes, at `θ = -(j + 1)`, is `0` by the convention `x / 0 = 0`.
