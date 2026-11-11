/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.FiniteBalance
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-!
# Tests for `MathlibExt.LinearAlgebra.FiniteBalance`

Exact integer `*ᵥ` arithmetic by `decide`; a coordinate functional that fails the column
hypothesis and one that satisfies it; reindexing along `finRotate 3` over `ℚ`; rank-nullity for
the zero and identity maps on `Fin 2 → ℝ`; and the two-reaction network
`2 H₂ + O₂ → 2 H₂O`, `H₂ + O₂ → H₂O₂`, whose element balances are unchanged by any real
extents.
-/

open scoped Matrix

namespace MathlibExtTest.LinearAlgebra.FiniteBalance

open MathlibExt.LinearAlgebra.FiniteBalance

/-! ### Exact matrix-vector arithmetic -/

/-- `[[1, 2, 3], [4, 5, 6]] *ᵥ (1, 0, -1) = (-2, -2)`, by exact integer evaluation. -/
example : !![(1 : ℤ), 2, 3; 4, 5, 6] *ᵥ ![1, 0, -1] = ![-2, -2] := by decide

/-- Carbon and oxygen counts of `CO, O₂, CO₂`: `2 CO + O₂ → 2 CO₂` is balanced. -/
example : !![(1 : ℤ), 0, 1; 1, 2, 2] *ᵥ ![-2, -1, 2] = 0 := by decide

/-- `CO + O₂ → CO₂` is not balanced: it loses one oxygen atom. -/
example : !![(1 : ℤ), 0, 1; 1, 2, 2] *ᵥ ![-1, -1, 1] = ![0, -1] := by decide

/-- A `2 × 3` real matrix whose second row vanishes. -/
def sampleMatrix : Matrix (Fin 2) (Fin 3) ℝ := !![1, 2, 3; 0, 0, 0]

/-- The first coordinate functional is nonzero on column `0` of `sampleMatrix`. -/
example : (LinearMap.proj 0 : (Fin 2 → ℝ) →ₗ[ℝ] ℝ) (fun b => sampleMatrix b 0) ≠ 0 := by
  simp [sampleMatrix]

/-- Hence it fails the column hypothesis of `map_mulVec_eq_zero_of_forall_col_eq_zero`. -/
example : ¬ ∀ s, (LinearMap.proj 0 : (Fin 2 → ℝ) →ₗ[ℝ] ℝ) (fun b => sampleMatrix b s) = 0 := by
  intro h
  simpa [sampleMatrix] using h 0

/-! ### Reindexing a weighted sum -/

/-- Rotating the indices of `w = (1/2, -3, 2)` and `x = (4, 1/3, -1)` leaves
`∑ j, w j * x j = 2 - 1 - 2 = -1` unchanged. -/
example :
    ∑ i, (![1 / 2, -3, 2] : Fin 3 → ℚ) (finRotate 3 i) *
      (![4, 1 / 3, -1] : Fin 3 → ℚ) (finRotate 3 i) = -1 := by
  rw [weightedSum_comp_equiv (finRotate 3)]
  norm_num [Fin.sum_univ_three]

/-! ### A coordinate functional vanishing on every column -/

/-- The second coordinate functional vanishes on every column of `sampleMatrix`, hence on
`sampleMatrix *ᵥ (1, -1, 2)`. -/
example : (LinearMap.proj 1 : (Fin 2 → ℝ) →ₗ[ℝ] ℝ) (sampleMatrix *ᵥ ![1, -1, 2]) = 0 := by
  have hcol : ∀ s, (LinearMap.proj 1 : (Fin 2 → ℝ) →ₗ[ℝ] ℝ) (fun b => sampleMatrix b s) = 0 := by
    intro s
    fin_cases s <;> simp [sampleMatrix]
  exact map_mulVec_eq_zero_of_forall_col_eq_zero _ sampleMatrix hcol _

/-! ### Rank-nullity for the zero and identity maps -/

/-- The zero map on `Fin 2 → ℝ` has a `2`-dimensional kernel and a `0`-dimensional range. -/
example :
    Module.finrank ℝ (LinearMap.ker (0 : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ))) = 2 ∧
      Module.finrank ℝ (LinearMap.range (0 : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ))) = 0 := by
  have h := finrank_ker_add_finrank_range (0 : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ))
  have h0 : Module.finrank ℝ (LinearMap.range (0 : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ))) = 0 := by
    rw [LinearMap.range_zero, finrank_bot]
  rw [Fintype.card_fin] at h
  omega

/-- The identity map on `Fin 2 → ℝ` has a `0`-dimensional kernel and a `2`-dimensional
range. -/
example :
    Module.finrank ℝ (LinearMap.ker (LinearMap.id : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ))) = 0 ∧
      Module.finrank ℝ (LinearMap.range (LinearMap.id : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ))) = 2 := by
  have h := finrank_ker_add_finrank_range (LinearMap.id : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ))
  have h0 :
      Module.finrank ℝ (LinearMap.ker (LinearMap.id : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ))) = 0 := by
    rw [LinearMap.ker_id, finrank_bot]
  rw [Fintype.card_fin] at h
  omega

/-! ### A two-reaction network -/

/-- Element counts (rows `H, O`) of the species `H₂, O₂, H₂O, H₂O₂` (columns). -/
def composition : Matrix (Fin 2) (Fin 4) ℝ := !![2, 0, 2, 2; 0, 2, 1, 2]

/-- Reaction columns `2 H₂ + O₂ → 2 H₂O` and `H₂ + O₂ → H₂O₂`; reactants have negative
coefficients. -/
def reactions : Matrix (Fin 4) (Fin 2) ℝ := !![-2, -1; -1, -1; 2, 0; 0, 1]

/-- The species change produced by extents `ξ` is the extent-weighted sum of the two reaction
columns. -/
example (ξ : Fin 2 → ℝ) :
    reactions *ᵥ ξ = ξ 0 • (fun b => reactions b 0) + ξ 1 • (fun b => reactions b 1) := by
  rw [mulVec_eq_sum_smul_col, Fin.sum_univ_two]

/-- Each element balance vanishes on both reaction columns, so the balance coordinates
`composition *ᵥ n` are unchanged by any real extents `ξ`. -/
example (n₀ : Fin 4 → ℝ) (ξ : Fin 2 → ℝ) :
    composition *ᵥ (n₀ + reactions *ᵥ ξ) = composition *ᵥ n₀ := by
  have hcol : ∀ e r,
      (LinearMap.proj e ∘ₗ composition.mulVecLin) (fun b => reactions b r) = 0 := by
    intro e r
    fin_cases e <;> fin_cases r <;>
      norm_num [composition, reactions, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  ext e
  have h := map_mulVec_eq_zero_of_forall_col_eq_zero _ reactions (hcol e) ξ
  rw [LinearMap.comp_apply, Matrix.mulVecLin_apply, LinearMap.proj_apply] at h
  rw [Matrix.mulVec_add, Pi.add_apply, h, add_zero]

end MathlibExtTest.LinearAlgebra.FiniteBalance

#print axioms MathlibExt.LinearAlgebra.FiniteBalance.weightedSum_comp_equiv
#print axioms MathlibExt.LinearAlgebra.FiniteBalance.finrank_ker_add_finrank_range
#print axioms MathlibExt.LinearAlgebra.FiniteBalance.mulVec_eq_sum_smul_col
#print axioms MathlibExt.LinearAlgebra.FiniteBalance.map_mulVec_eq_zero_of_forall_col_eq_zero
