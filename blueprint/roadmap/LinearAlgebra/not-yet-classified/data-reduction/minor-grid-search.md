# The first grid value preserving a minor

Let F be a field, A₀,…,Aₘ₋₁ ∈ Mat(k,l;F), and fix injections selecting r rows and r columns.
Write M(θ) for the determinant of that r × r minor of ∑ᵢ θᵢAᵢ. Let g : Fin N → F be an ordered
scalar grid. For a coordinate i, coefficient tuple θ and a list L of grid indices, search L in
order for t with M(θ[i ↦ g(t)]) ≠ 0. Return the first such index, or none if it does not
exist, together with the list of indices tested up to success or exhaustion.
