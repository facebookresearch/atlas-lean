# Reducing a list of coefficient coordinates

Let F be a field, A₀,…,Aₘ₋₁ ∈ Mat(k,l;F), and fix injections selecting r rows and r columns.
Write M(θ) for the determinant of that r × r minor of ∑ᵢ θᵢAᵢ. Let g : Fin N → F be an ordered
scalar grid. Given a list of coordinates and an initial θ, replace each listed coordinate by
the first grid value preserving M ≠ 0, in grid-index order. Return the final tuple if all
searches succeed, or none at the first failure, together with the sequence of tested
coordinate/index pairs.
