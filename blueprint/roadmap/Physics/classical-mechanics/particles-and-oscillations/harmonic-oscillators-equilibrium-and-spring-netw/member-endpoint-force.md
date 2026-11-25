# Internal endpoint forces of an axial-member table

Let `J` be a set of joints with positions `r : J → ℝ²`, `M` a set of members, member `e` joining
the joints `a(e)` and `b(e)`, and `c : M → ℝ` signed coefficients. The internal force at the
endpoint `(e, false)` (the joint `a(e)`) is `c(e) (r(b(e)) - r(a(e)))`, and at `(e, true)` (the
joint `b(e)`) its negative `-c(e) (r(b(e)) - r(a(e)))`: the force the member exerts on each joint,
along the separation vector. Positive `c(e)` pulls the two joints towards each other (tension).
The formula is defined for every table; when `r(a(e)) = r(b(e))` both forces are `0`. For a
genuine two-force member the endpoints are distinct and `c(e)` is the axial force divided by the
member length. External loads are not part of this internal-force family.
