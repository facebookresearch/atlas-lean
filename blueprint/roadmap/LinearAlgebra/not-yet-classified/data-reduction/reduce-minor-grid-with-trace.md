# The full coefficient scan and its test sequence

Let F be a field, A₀,…,Aₘ₋₁ ∈ Mat(k,l;F), and fix injections selecting r rows and r columns.
Write M(θ) for the determinant of that r × r minor of ∑ᵢ θᵢAᵢ. Let g : Fin N → F be an ordered
scalar grid. Starting from β, scan coordinates 0,…,m−1, replacing each by the first grid value
retaining a nonzero selected minor. The output is an optional coefficient tuple paired with
the sequence of tested coordinate/grid-index pairs.
