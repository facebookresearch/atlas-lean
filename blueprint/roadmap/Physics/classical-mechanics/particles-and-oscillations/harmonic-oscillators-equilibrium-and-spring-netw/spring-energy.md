# Energy of a finite spring network

Let `ι` be a finite set of nodes with scalar displacements `u : ι → ℝ`, pair weights
`k : ι → ι → ℝ` and wall stiffnesses `w : ι → ℝ` (a spring from node `i` to a fixed wall). The
spring-network energy is

`U(k, w, u) = (1/4) ∑_{i ∈ ι} ∑_{j ∈ ι} k_{ij} (u_j - u_i)² + (1/2) ∑_{i ∈ ι} w_i u_i²`.

`w = 0` is a free network and `w_i > 0` a node fixed to the wall. The definition accepts any real
weights. For reciprocal weights `k_{ij} = k_{ji}` the ordered double sum counts each spring twice,
so each pair `{i, j}` contributes `(1/2) k_{ij} (u_j - u_i)²`; for general weights the pair
`{i, j}` contributes with the average weight `(k_{ij} + k_{ji}) / 2`, and diagonal terms always
vanish. In the physical reading the weights and wall stiffnesses are nonnegative.
