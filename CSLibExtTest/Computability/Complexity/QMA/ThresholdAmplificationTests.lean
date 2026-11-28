/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.QMA.ThresholdAmplification

/-!
# Tests: Threshold amplification of an acceptance operator
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder
namespace CslibTest.Complexity.Classes.QMA

set_option autoImplicit false

open Cslib.Complexity.Classes Cslib.Complexity.Classes.QMA

#print axioms tailWeight_le_exp
#print axioms one_sub_exp_le_tailWeight
#print axioms re_star_dotProduct_thresholdOp_mulVec_le_exp
#print axioms one_sub_exp_le_re_star_dotProduct_thresholdOp_mulVec_blockProd
#print axioms two_mul_le_amplifyCount_mul_sq
#print axioms thresholdOp_amplify_sound
#print axioms thresholdOp_amplify_complete
#print axioms thresholdOp_one_submatrix

/-- Boundary: at threshold `0` one block has weight `1`, not its parameter. -/
theorem tailWeight_one_block_zero : tailWeight (fun _ : Fin 1 => (1 / 3 : ℝ)) 0 = 1 := by
  have hnonneg : ∀ x ∈ (Finset.univ : Finset (Fin 1 → Bool)),
      (0 : ℝ) ≤ acceptCount x := by
    intro x _
    unfold acceptCount
    apply Finset.sum_nonneg
    intro i _
    split_ifs <;> norm_num
  unfold tailWeight
  rw [Finset.filter_true_of_mem hnonneg]
  have he : ∀ (a : Bool) (i : Fin 1),
      ((Equiv.piUnique (fun _ : Fin 1 => Bool)).symm a) i = a :=
    fun a i => rfl
  rw [← Equiv.sum_comp (Equiv.piUnique (fun _ : Fin 1 => Bool)).symm]
  simp only [he, Fin.prod_univ_one, Fintype.sum_bool]
  norm_num
#print axioms tailWeight_one_block_zero

/-- Boundary: above one accepting block the weight is `0`. -/
theorem tailWeight_one_block_two : tailWeight (fun _ : Fin 1 => (1 / 3 : ℝ)) 2 = 0 := by
  unfold tailWeight
  rw [Finset.sum_filter]
  apply Finset.sum_eq_zero
  intro x _
  have hle : acceptCount x ≤ 1 := by
    unfold acceptCount
    simp only [Fin.sum_univ_one]
    split_ifs <;> norm_num
  split_ifs with h
  · have h2 : (2 : ℝ) ≤ (1 : ℝ) := h.trans hle
    norm_num at h2
  · rfl
#print axioms tailWeight_one_block_two

/-- `k = 2`, `Q = 0`, `s = 0`, `T = 1`: every unit two-block vector, entangled or not, has
threshold expectation at most `exp (-1)`. -/
theorem thresholdAmplify_two_block_sound (Ψ : Fin (2 ^ (2 * 1)) → ℂ) (hΨ : sqNorm Ψ = 1) :
    (star Ψ ⬝ᵥ (thresholdOp 2 (0 : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ) 1 *ᵥ Ψ)).re ≤
      Real.exp (-1) := by
  have hQ0 : (0 : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ).PosSemidef :=
    Matrix.PosSemidef.zero
  have hQ1 : (1 - (0 : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ)).PosSemidef := by
    simpa using Matrix.PosSemidef.one
  have hs : ∀ ψ : Fin (2 ^ 1) → ℂ, sqNorm ψ = 1 →
      (star ψ ⬝ᵥ (0 : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ) *ᵥ ψ).re ≤ 0 := by
    intro ψ _
    simp
  have h := re_star_dotProduct_thresholdOp_mulVec_le_exp (k := 2) (s := 0) (T := 1)
    hQ0 hQ1 hs (by norm_num) Ψ hΨ
  have hB : (-2 : ℝ) * (1 - ((2 : ℕ) : ℝ) * 0) ^ 2 / ((2 : ℕ) : ℝ) = -1 := by
    norm_num
  rw [hB] at h
  exact h
#print axioms thresholdAmplify_two_block_sound

/-- Promise `(2/3, 1/3)`, gap `1/3`, `p = 1`: `amplifyCount 1 3 = 18` copies at threshold `9` give
soundness at most `1/2` against every unit `18`-block vector. -/
theorem thresholdAmplify_promise_sound (Ψ : Fin (2 ^ (amplifyCount 1 3 * 1)) → ℂ)
    (hΨ : sqNorm Ψ = 1) :
    (star Ψ ⬝ᵥ (thresholdOp (amplifyCount 1 3) (0 : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ)
      ((amplifyCount 1 3 : ℝ) * (2 / 3 + 1 / 3) / 2) *ᵥ Ψ)).re ≤ 1 / 2 := by
  have hQ0 : (0 : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ).PosSemidef :=
    Matrix.PosSemidef.zero
  have hQ1 : (1 - (0 : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ)).PosSemidef := by
    simpa using Matrix.PosSemidef.one
  have hs : ∀ ψ : Fin (2 ^ 1) → ℂ, sqNorm ψ = 1 →
      (star ψ ⬝ᵥ (0 : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ) *ᵥ ψ).re ≤ 1 / 3 := by
    intro ψ _
    have h0 : (star ψ ⬝ᵥ (0 : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ) *ᵥ ψ).re
        = 0 := by
      simp
    rw [h0]
    norm_num
  have h := thresholdOp_amplify_sound (p := 1) (k := amplifyCount 1 3)
    (s := 1 / 3) (c := 2 / 3) hQ0 hQ1 (by norm_num)
    (by unfold amplifyCount; norm_num) hs Ψ hΨ
  simpa using h
#print axioms thresholdAmplify_promise_sound

/-- Same parameters: completeness at least `1/2` for the product witness. -/
theorem thresholdAmplify_promise_complete (ψ : Fin (2 ^ 1) → ℂ) (hψ : sqNorm ψ = 1) :
    1 / 2 ≤ (star (blockProd (fun _ : Fin (amplifyCount 1 3) => ψ)) ⬝ᵥ
      (thresholdOp (amplifyCount 1 3) (1 : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ)
        ((amplifyCount 1 3 : ℝ) * (2 / 3 + 1 / 3) / 2) *ᵥ
          blockProd (fun _ : Fin (amplifyCount 1 3) => ψ))).re := by
  have hQ0 : (1 : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ).PosSemidef :=
    Matrix.PosSemidef.one
  have hQ1 : (1 - (1 : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ)).PosSemidef := by
    simpa using Matrix.PosSemidef.zero
  have hc : ∀ φ : Fin (2 ^ 1) → ℂ, sqNorm φ = 1 →
      (2 / 3 : ℝ) ≤
        (star φ ⬝ᵥ (1 : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ) *ᵥ φ).re := by
    intro φ hφ
    rw [Matrix.one_mulVec, ← sqNorm_eq_re_star_dotProduct, hφ]
    norm_num
  have h := thresholdOp_amplify_complete (p := 1) (k := amplifyCount 1 3)
    (s := 1 / 3) (c := 2 / 3) hQ0 hQ1 (by norm_num)
    (by unfold amplifyCount; norm_num) ψ hψ (hc ψ hψ)
  have hnum : (1 : ℝ) - ((2 : ℝ) ^ 1)⁻¹ = 1 / 2 := by norm_num
  rw [hnum] at h
  exact h
#print axioms thresholdAmplify_promise_complete

/-- The repetition count at `p = 1`, `q = 3` is `18`. -/
theorem amplifyCount_one_three : amplifyCount 1 3 = 18 := by
  rfl
#print axioms amplifyCount_one_three

/-- The `(2/3, 1/3)` gap meets the count bound at `p = 1`, `q = 3`. -/
theorem two_mul_le_amplifyCount_example :
    2 * (1 : ℝ) ≤ (amplifyCount 1 3 : ℝ) * (2 / 3 - 1 / 3) ^ 2 := by
  have h := two_mul_le_amplifyCount_mul_sq (p := 1) (q := 3) (c := 2 / 3) (s := 1 / 3)
    (by norm_num)
  simpa using h
#print axioms two_mul_le_amplifyCount_example

/-- One block at threshold `1/2` of `Q = 0` acts as `0` entrywise. -/
theorem thresholdOp_one_submatrix_apply (i j : Fin (2 ^ 1)) :
    ((thresholdOp 1 (0 : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ) (1 / 2)).submatrix
      (Fin.cast (by rw [Nat.one_mul]) : Fin (2 ^ 1) → Fin (2 ^ (1 * 1)))
      (Fin.cast (by rw [Nat.one_mul]) : Fin (2 ^ 1) → Fin (2 ^ (1 * 1)))) i j =
      (0 : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ) i j := by
  have h := thresholdOp_one_submatrix (0 : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ)
    (T := 1 / 2) (by norm_num) (by norm_num)
  exact congrFun (congrFun h i) j
#print axioms thresholdOp_one_submatrix_apply

/-- The `k = 0`, `p = 0` soundness instance bounds every unit vector by `1`. -/
theorem thresholdAmplify_zero_block_sound (Ψ : Fin (2 ^ (0 * 1)) → ℂ)
    (hΨ : sqNorm Ψ = 1) :
    (star Ψ ⬝ᵥ (thresholdOp 0 (0 : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ)
      (((0 : ℕ) : ℝ) * (0 + 0) / 2) *ᵥ Ψ)).re ≤ 1 := by
  have hQ0 : (0 : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ).PosSemidef :=
    Matrix.PosSemidef.zero
  have hQ1 : (1 - (0 : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ)).PosSemidef := by
    simpa using Matrix.PosSemidef.one
  have hs : ∀ ψ : Fin (2 ^ 1) → ℂ, sqNorm ψ = 1 →
      (star ψ ⬝ᵥ (0 : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ) *ᵥ ψ).re ≤ 0 := by
    intro ψ _
    simp
  have h := thresholdOp_amplify_sound (k := 0) (p := 0) hQ0 hQ1 (c := 0) (s := 0)
    (by norm_num) (by norm_num) hs Ψ hΨ
  simpa using h
#print axioms thresholdAmplify_zero_block_sound

end CslibTest.Complexity.Classes.QMA
