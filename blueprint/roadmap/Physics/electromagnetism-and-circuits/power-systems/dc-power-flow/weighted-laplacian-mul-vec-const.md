# The weighted Laplacian annihilates constant angle vectors

Consider a network with nodes `0, …, n_N - 1` and branches `0, …, n_E - 1`, branch `e` running from
its tail `t(e)` to its head `h(e)` (loops `t(e) = h(e)` and parallel branches allowed). For real
branch susceptances `b_e` of any sign and every real constant `c`, the
[susceptance-weighted Laplacian](weighted-laplacian.md) `L_b` maps the constant vector `(c, …, c)`
to zero. Hence adding the same constant to every angle leaves the
[DC injections `L_b θ`](dc-injection-eq-weighted-laplacian-mul-v.md) unchanged; the branch flows
[`b_e (θ_{t(e)} - θ_{h(e)})`](dc-branch-flow-apply.md) are unchanged as well. Unlike the
[kernel characterisation](weighted-laplacian-mul-vec-eq-zero-iff.md), this needs no sign condition
on the susceptances.
