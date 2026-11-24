# The reconstruction is the amplitude times the unit Galerkin solution

For a [partition](../../real-functions/integration/riemann-integral/partition.md) `P` of `[0, 1]`
and nodal values `c` forming a
[Galerkin solution](../finite-element-method-in-one-dimension/is-galerkin-solution.md) of the unit
problem `-û'' = 2` on `P`, and all real `EA`, `L`, `q` and `x`, the [reconstruction](physical-p1.md)
satisfies `u_h(x) = α p_c(x / L)`, where `p_c` is the
[piecewise linear function](../finite-element-method-in-one-dimension/p1.md) with nodal values `c`.
