# Stiffness matrix of a finite spring network

For a finite set `ι` of nodes, pair weights `k : ι → ι → ℝ` and wall stiffnesses `w : ι → ℝ`, the
stiffness matrix `K` has entries

`K_{ii} = (∑_{l ∈ ι} k_{il}) + w_i` and `K_{ij} = -k_{ij}` for `i ≠ j`.

The diagonal sum includes `k_{ii}`. Without self-springs (`k_{ii} = 0`), `-(K u)_i` is the total
spring force `∑_j k_{ij} (u_j - u_i) - w_i u_i` on node `i`; for reciprocal weights without
self-springs (`k_{ij} = k_{ji}` and `k_{ii} = 0`), half the quadratic form `uᵀ K u` is the
[spring energy](spring-energy.md) ([identity](spring-energy-eq-quad-form.md)).
