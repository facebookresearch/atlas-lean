# A dispatch is feasible iff it decodes a feasible LP point

Consider a network with finitely many buses `v` and branches `e` (each with a tail and a head bus
and a real susceptance `b_e`), finitely many generators `g` placed at buses, a demand `d`, a
reference bus `r`, generator limits `p_min`, `p_max` and branch-flow limits `f_min`, `f_max`. A
generation `p` and angles `θ` form a [feasible dispatch](is-dispatch-feasible.md) if and only if
some feasible point of the [dispatch linear program](lp-matrix.md): a vector `x ≥ 0` with
`A x ≤ rhs` for the [constraint matrix](lp-matrix.md) `A` and the [right-hand side](lp-rhs.md)
decodes to them ([generation](decode-generation.md) `p`, [angles](decode-angle.md) `θ`). The split
into positive and negative parts is not unique, so the converse direction is existential.
