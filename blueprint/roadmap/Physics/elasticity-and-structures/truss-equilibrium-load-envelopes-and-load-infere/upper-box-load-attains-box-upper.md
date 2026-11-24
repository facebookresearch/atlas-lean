# The upper endpoint load attains the upper envelope

Let `ι` be a finite set of load coordinates, `η` a fixed influence vector and `cap` a vector of
pattern capacities, both indexed by `ι`, with `cap_i ≥ 0` for all `i`. The
[upper endpoint load](upper-box-load.md) `f` lies in the box, `0 ≤ f_i ≤ cap_i` for all `i`, and its
response `η · f` equals the upper envelope value `∑_i cap_i * max(η_i, 0)`, so the
[upper envelope bound](dot-product-le-box-upper.md) is attained. The nonnegativity of the capacities
makes the endpoint load feasible.
