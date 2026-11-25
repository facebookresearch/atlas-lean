# Harmonic measure

Let Ω⊂ℝⁿ be a bounded domain and let x∈Ω.

The harmonic measure ω_Ωˣ is the probability measure concentrated on ∂Ω which represents the
generalized Dirichlet solution.

More precisely, for every continuous boundary datum f:∂Ω→ℝ, one has

H_f(x)=∫_\{∂Ω\} f dω_Ωˣ,

where H_f is the Perron, or generalized, solution of the Dirichlet problem on Ω with boundary data
f.

For continuous finite-valued boundary data on a bounded Euclidean domain, the Perron solution is
finite, so although the formal `upperPerronSolution` is naturally `EReal`-valued, its value in this
representation agrees with the coercion to `EReal` of the ordinary real-valued integral.
