# The output of grid reduction

Let F be a field, A₀,…,Aₘ₋₁ ∈ Mat(k,l;F), and fix injections selecting r rows and r columns.
Write M(θ) for the determinant of that r × r minor of ∑ᵢ θᵢAᵢ. Let g : Fin N → F be an ordered
scalar grid. The reduction map returns the optional tuple produced by scanning all m
coordinates in order and selecting the first grid value at each coordinate for which the
selected determinant stays nonzero.
