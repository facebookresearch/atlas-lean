# Trace of a product of two matrix functions

Let `A` and `B` be Hermitian matrices over
`ℝ` or `ℂ`, with spectral decompositions `A = U diag(λ) U*` and `B = V diag(μ) V*` given by
Mathlib's `Matrix.IsHermitian.eigenvalues` and `Matrix.IsHermitian.eigenvectorUnitary`. For all
functions `f g : ℝ → ℝ`, `tr (f(A) g(B)) = ∑ᵢ ∑ⱼ f(λᵢ) g(μⱼ) |(U* V)ᵢⱼ|²`, where `f(A) = cfc f A`
and `g(B) = cfc g B` are the standard matrix functions (the computation in the proof of
J. A. Tropp, *An Introduction to Matrix Concentration Inequalities*, arXiv:1501.01571v1,
Proposition 8.3.5).
