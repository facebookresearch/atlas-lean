# Internal axial-member forces have zero resultant

Let `J` be a set of joints with positions `r : J → ℝ²`, `M` a finite set of members, member `e`
joining the joints `a(e)` and `b(e)`, and `c : M → ℝ` coefficients. Then the
[internal endpoint forces](member-endpoint-force.md) `c(e) (r(b(e)) - r(a(e)))` at `a(e)` and
`-c(e) (r(b(e)) - r(a(e)))` at `b(e)` have zero [resultant](resultant-force.md): each member
contributes an equal and opposite pair.
