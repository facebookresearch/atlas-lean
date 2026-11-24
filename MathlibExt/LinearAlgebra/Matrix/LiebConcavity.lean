/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.RelativeEntropy

/-!
# Lieb's concavity theorem

For a Hermitian matrix `H`, the map `A ↦ tr exp(H + log A)` is concave on the cone of
positive-definite matrices (E. H. Lieb, *Convex trace functions and the Wigner–Yanase–Dyson
conjecture*, Adv. Math. 11 (1973), 267–288, Theorem 6), where `log A = cfc Real.log A`. Its
best-known use is in matrix concentration: with Jensen's inequality it makes matrix cumulant
generating functions subadditive (J. A. Tropp, *An Introduction to Matrix Concentration
Inequalities*, Found. Trends Mach. Learn. 8 (2015), arXiv:1501.01571v1, Theorem 3.4.1,
Corollary 3.4.2 and Lemma 3.5.1).

## Proof

The proof is Tropp's derivation from the joint convexity of the matrix relative entropy
(J. A. Tropp, *From joint convexity of quantum relative entropy to a concavity theorem of Lieb*,
Proc. Amer. Math. Soc. 140 (2012), 1757–1760, arXiv:1101.1070v1, proof of Theorem 1; Tropp,
*An Introduction to Matrix Concentration Inequalities*, Section 8.1.4). With
`D(X, A) = re tr (X log X) - re tr (X log A)`, the variational formula
`MathlibExt.LinearAlgebra.Matrix.RelativeEntropy.isGreatest_re_trace_exp` applied to
`M = H + log A` gives
`re tr exp(H + log A) = max_{X ≻ 0} [re tr (X H) + re tr X - D(X, A)]`.
The bracket is jointly concave in `(X, A)` by
`MathlibExt.LinearAlgebra.Matrix.RelativeEntropy.convexOn_relativeEntropy`, and a partial maximum
of a jointly concave function is concave: at `A = a A₁ + b A₂`, evaluate the bracket at
`X = a X₁ + b X₂`, where `Xₖ` attains the maximum at `Aₖ`.

The theorem keeps the full name it had when it was recorded as wanted, so its namespace still
reads `LiebConcavityWanted`.
-/

@[expose] public section

open scoped ComplexOrder

namespace MathlibExt.LinearAlgebra.Matrix.LiebConcavityWanted

open MathlibExt.LinearAlgebra.Matrix.RelativeEntropy

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Lieb's concavity theorem** (E. H. Lieb, *Convex trace functions and the Wigner–Yanase–Dyson
conjecture*, Adv. Math. 11 (1973), 267–288, Theorem 6; Tropp, *An Introduction to Matrix
Concentration Inequalities*, arXiv:1501.01571, Theorem 3.4.1 and Theorem 8.1.1). For a fixed
Hermitian matrix `H`, the map `A ↦ tr exp(H + log A)` is concave on the cone of positive-definite
matrices. Here `log A` is the standard matrix function `cfc Real.log A`. -/
theorem lieb_concavity {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    ConcaveOn ℝ {A : Matrix n n ℂ | A.PosDef}
      (fun A => RCLike.re (NormedSpace.exp (H + cfc Real.log A)).trace) := by
  refine ⟨Matrix.convex_setOfPred_posDef, fun A₁ hA₁ A₂ hA₂ a b ha hb hab => ?_⟩
  have hM : ∀ A : Matrix n n ℂ, (H + cfc Real.log A).IsHermitian := fun A =>
    hH.add (cfc_predicate Real.log A)
  -- maximizers of the variational formula at `A₁` and `A₂`
  obtain ⟨⟨X₁, hX₁, e₁⟩, -⟩ := isGreatest_re_trace_exp (hM A₁)
  obtain ⟨⟨X₂, hX₂, e₂⟩, -⟩ := isGreatest_re_trace_exp (hM A₂)
  -- the variational formula at `a A₁ + b A₂`, evaluated at `a X₁ + b X₂`
  have hle := (isGreatest_re_trace_exp (hM (a • A₁ + b • A₂))).2
    ⟨a • X₁ + b • X₂, Matrix.convex_setOfPred_posDef hX₁ hX₂ ha hb hab, rfl⟩
  have hconv := (convexOn_relativeEntropy (𝕜 := ℂ)).2 (x := (X₁, A₁)) (y := (X₂, A₂))
    ⟨hX₁, hA₁⟩ ⟨hX₂, hA₂⟩ ha hb hab
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at hconv
  simp only at e₁ e₂ hle ⊢
  rw [← e₁, ← e₂]
  refine le_trans ?_ hle
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add,
    Matrix.trace_smul, map_add, RCLike.smul_re, smul_eq_mul] at hconv ⊢
  nlinarith [hconv]

end MathlibExt.LinearAlgebra.Matrix.LiebConcavityWanted
