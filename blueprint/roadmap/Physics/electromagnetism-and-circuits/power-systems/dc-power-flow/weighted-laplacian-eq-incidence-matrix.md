# The weighted Laplacian in terms of the head-positive incidence

Consider a network with nodes `0, …, n_N - 1` and branches `0, …, n_E - 1`, branch `e` running from
its tail `t(e)` to its head `h(e)` (loops `t(e) = h(e)` and parallel branches allowed), with real
branch susceptances `b_e`. Let `A = -B` be the head-positive incidence matrix,
`A_{ve} = [h(e) = v] - [t(e) = v]`, where `B` is the
[electrical incidence](../../circuit-theory/tellegen-s-theorem-and-branch-power-balance/electrical-incidence.md).
Then the [susceptance-weighted Laplacian](weighted-laplacian.md) satisfies

`L_b = B diag(b) Bᵀ = A diag(b) Aᵀ`,

since the two sign changes cancel. So `L_b` is the weighted Laplacian `A diag(w) Aᵀ` of the arc
network with weights `w = b`, as in
[graph Laplacians](../../../../GraphTheory/algebraic-graph-theory/part-01/graph-laplacians-and-cheeger-s-inequality/README.md).
The identity holds for all real `b`.
