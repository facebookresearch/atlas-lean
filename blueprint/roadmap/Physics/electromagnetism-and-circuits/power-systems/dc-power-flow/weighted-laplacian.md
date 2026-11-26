# Susceptance-weighted Laplacian

Consider a network with nodes `0, …, n_N - 1` and branches `0, …, n_E - 1`, branch `e` running from
its tail `t(e)` to its head `h(e)` (loops `t(e) = h(e)` and parallel branches allowed), with real
branch susceptances `b_e`. The susceptance-weighted Laplacian is the real `n_N × n_N` matrix

`L_b = B diag(b) Bᵀ`,

where `B` is the
[electrical incidence](../../../../GraphTheory/algebraic-graph-theory/part-01/oriented-incidence-matrices/oriented-incidence.md),
with no reference row or column deleted. Its diagonal entry at `v` is the sum of `b_e` over the
branches incident to `v` that are not loops, and its entry at `(u, v)` with `u ≠ v` is minus the sum
of `b_e` over the branches joining `u` and `v` in either orientation. It is the
[weighted Laplacian of the multigraph](../../../../GraphTheory/algebraic-graph-theory/part-01/graph-laplacians-and-cheeger-s-inequality/laplacian.md)
whose edges are the branches, each from its tail to its head, with weights `b`. An inductive branch,
of series reactance `x_e > 0`, has positive susceptance `b_e = 1/x_e`; the definition allows all
real `b`.
