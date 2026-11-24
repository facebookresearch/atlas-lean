# Member Endpoint Force

Internal endpoint force of one axial member table entry,
read as the force the member exerts on the joint. For member
`e`, `c e` is the signed coefficient along the separation
vector `r (b e) - r (a e)`: the force at `a e` is
`c e • (r (b e) - r (a e))` and the force at `b e` is its
negative, so positive `c e` is tension. This separation-vector
form is the totalized model; for a genuine two-force member the
endpoints are distinct and `c e` is the axial force divided by
the member length. Joint-only loading is the physical reason a
pin-jointed member carries only such an endpoint axial pair;
external loads are outside this internal-force sum.
