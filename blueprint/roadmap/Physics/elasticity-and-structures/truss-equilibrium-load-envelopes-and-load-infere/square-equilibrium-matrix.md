# Square equilibrium matrix of a planar truss

Let `J` (joints), `M` (members) and `R` (reaction components) be finite sets, with joint positions
`r_j` in the plane, member `e` joining joint `a_e` to joint `b_e`, and reaction component `s` acting
at joint `sj_s` along the direction `sd_s` (a vector of the plane, not necessarily of unit length).
Given a bijection `e` from the unknowns (the members, then the reaction components) to the joint
coordinates, the square equilibrium matrix is the [equilibrium matrix](equilibrium-matrix.md) with
its rows renumbered: its row `u` is row `e(u)` of the equilibrium matrix, and its columns are the
unknowns.
