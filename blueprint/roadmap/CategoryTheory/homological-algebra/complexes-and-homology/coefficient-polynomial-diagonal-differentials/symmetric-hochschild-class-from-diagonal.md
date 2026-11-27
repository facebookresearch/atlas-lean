# A diagonal coefficient element defines a Hochschild class

Let k be a commutative ring, σ any variable set and A = k[σ]. Put E = A ⊗[k] Aᵐᵒᵖ, V = ⊕ᵢ∈σ E·eᵢ
and δᵢ = Xᵢ ⊗ 1 − 1 ⊗ Xᵢᵐᵒᵖ. Let M be an A-module with compatible k-action, regarded as a
symmetric A-bimodule. In degree n : ℕ, take a diagonal term z ∈ M ⊗_E ∧ⁿ_EV to its homology
class in the zero-differential diagonal complex, then apply the homology map of
symmetricCoefficientComparison.inv. This defines symmetricHochschildClassFromDiagonal : M ⊗_E
∧ⁿ_EV → HHₙ(A,M).
