# The infinite-sites sampling formula in the marked Kingman model

For `θ ≥ 0`, every natural number `n ≥ 2` and every natural number `m`, in the
[marked Kingman model](../poisson-mutation-on-the-kingman-genealogy/kingman-mutation-measure.md)
the number of segregating sites `S = ∑_b N_b` satisfies

`P(S = m) = (n - 1) ∑_{j=0}^{n-2} (-1)^j C(n - 2, j) θ^m / (θ + j + 1)^{m+1}`,

[Tavaré's formula](seg-sites-prob.md), with no further hypothesis. Powers are natural powers with
`θ^0 = 1`, also at `θ = 0`, where all the mass is at `m = 0`.
