# Combining the bounds for the theta function

Let `g` and `N` be natural numbers and `h`,
`L₁, …, L_N`, `D₁, …, D_N` real numbers such that `Lⱼ ≤ Dⱼ/4 + (3g³ + 5g) log 2` for each `j`
and `(1/N) ∑ⱼ Dⱼ ≤ g log max(1, h) + (2g³ + 2) log 2`. Then
`(1/N) ∑ⱼ Lⱼ ≤ (g/4) log max(1, h) + (4g³ + 5g + 1) log 2`.
The source has `g ≥ 1` and `N ≥ 1`; neither is needed (for `N = 0` both averages are `0`, as
`1/0 = 0` in Lean).

A. Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi curves*, Algebra Number
Theory 8 (2014), proof of Lemma 2.4.2, p. 100 ("Combining (5) with the upper bound (6) implies
the result"), with `N = [K : ℚ]`, `j` running over the embeddings `σ : K → ℂ`,
`Lσ = log max ‖ϑ‖` on `Pic_{g-1}(X_σ)`, `Dσ = log det Im(τσ)` and `h = h_Fal(X)`.
