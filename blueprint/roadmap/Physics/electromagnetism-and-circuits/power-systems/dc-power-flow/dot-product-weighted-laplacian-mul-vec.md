# Energy identity for the susceptance-weighted Laplacian

Consider a network with nodes `0, …, n_N - 1` and branches `0, …, n_E - 1`, branch `e` running from
its tail `t(e)` to its head `h(e)` (loops `t(e) = h(e)` and parallel branches allowed). For all real
branch susceptances `b_e` and node phase angles `θ_v`,

`θ · (L_b θ) = ∑_e b_e (θ_{t(e)} - θ_{h(e)})²`,

where `L_b` is the [susceptance-weighted Laplacian](weighted-laplacian.md): its quadratic form is
the susceptance-weighted sum of the squared angle differences across the branches. This is a special
case of the
[Laplacian quadratic form](../../../../GraphTheory/algebraic-graph-theory/part-01/graph-laplacians-and-cheeger-s-inequality/dot-product-mul-vec-laplacian.md).
In the physical reading the susceptances are positive, and the form is then nonnegative; the
identity holds for all real `b`.
