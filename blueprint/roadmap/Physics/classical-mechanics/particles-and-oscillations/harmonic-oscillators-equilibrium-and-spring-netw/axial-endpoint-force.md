# Endpoint forces of an axial-member table from axial forces

Let `J` be a set of joints with positions `r : J → ℝ²`, `M` a set of members, member `e` joining
the joints `a(e)` and `b(e)`, with [length](member-length.md) `ℓ(e)`, and `N : M → ℝ` axial forces.
The force at the endpoint `(e, false)` (the joint `a(e)`) is `N(e)` times the unit separation
vector, `N(e) ℓ(e)⁻¹ (r(b(e)) - r(a(e)))`, and at `(e, true)` (the joint `b(e)`) its negative.
Positive `N(e)` is tension. With the convention `0⁻¹ = 0`, both forces are `0` for a member whose
endpoints coincide; the two-force-member reading needs distinct endpoints, which give `ℓ(e) > 0`
([positive length](member-length-pos-of-ne.md)).
