# An injective truss equilibrium matrix forces distinct member endpoints

Consider a planar pin-jointed truss with joints `J` at positions `r_j ∈ ℝ²`, finitely many members
`M` joining the joints `a(e)` and `b(e)`, and finitely many support reactions `R` at the joints
`sj(s)` along the directions `sd(s) ∈ ℝ²`. If the
[equilibrium matrix](../../../elasticity-and-structures/truss-equilibrium-load-envelopes-and-load-infere/equilibrium-matrix.md)
is injective, then `r_{a(e)} ≠ r_{b(e)}` for every member `e`, so every member has
[positive length](../../particles-and-oscillations/harmonic-oscillators-equilibrium-and-spring-netw/member-length-pos-of-ne.md).
A member with coincident endpoints has a zero unit vector, by the convention `a / 0 = 0`, hence a
zero column, and a unit force in it would balance zero loads, a spurious state of self-stress.
