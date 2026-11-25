# Length of an axial member

Let `J` be a set of joints with positions `r : J → ℝ²` and `M` a set of members, member `e` joining
the joints `a(e)` and `b(e)`. The length of member `e` is the Euclidean distance between its
endpoints,

`ℓ(e) = √((r(b(e)) - r(a(e)))₀² + (r(b(e)) - r(a(e)))₁²)`.

It is `0` exactly when the endpoints coincide.
