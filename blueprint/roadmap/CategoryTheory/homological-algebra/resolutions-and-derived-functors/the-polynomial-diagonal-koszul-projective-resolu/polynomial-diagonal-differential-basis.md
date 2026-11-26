# Polynomial diagonal boundaries use signed difference-coefficient deletion

Let k be a commutative ring and σ any index type. Put A = MvPolynomial σ k, E = A ⊗[k] Aᵐᵒᵖ, V
= σ →₀ E and δ_i = X_i ⊗ 1 − 1 ⊗ op(X_i). For n : ℕ and any f : Fin (n + 1) → σ, write e_i for
the unit coordinate at i. The boundary of e_(f 0) ∧ … ∧ e_(f n) is ∑ j : Fin (n + 1), ((−1 :
E)^j * δ_(f j)) • (⋀ q : Fin n, e_(f(j.succAbove q))). The remaining coordinates retain their
order.
