/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPackedBoundaryData

/-! Ungated genuine source-slot bindings and full-coordinate packed Start/Finish implications. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

private theorem sign_abs (c : ZMod 2) : |generatedAxisGlobalIntSign c| = 1 := by
  unfold generatedAxisGlobalIntSign
  split_ifs <;> norm_num

/-- Complete original input word maxima bound every actual original coefficient. -/
theorem generatedTenth_packed_boundary_input_abs (hb : GeneratedTenthPackedBoundaryBounds)
    (n : Fin 4096) (j : Fin 24) : |generatedTenthTwoFixerTensorInput n j| ≤ 176 := by
  let a : Fin 256 := ⟨n.val / 16, by omega⟩
  let i : Fin 16 := ⟨n.val % 16, Nat.mod_lt _ (by decide)⟩
  have h := generatedTenth_packed_boundary_abs_max _ 176 (hb.1 j a) i
  rw [generatedTenth_packed_boundary_input_digit,
    generatedTenth_packed_boundary_prefix_recover] at h
  exact h

/-- The original stage-zero word maxima bound every actual output coefficient. -/
theorem generatedTenth_packed_boundary_zero_abs (hb : GeneratedTenthPackedBoundaryBounds)
    (g : Fin 2) (n : Fin 4096) (j : Fin 24) :
    |generatedTenthTwoFixerTensorState g 0 n j| ≤ 144 := by
  let a : Fin 256 := ⟨n.val / 16, by omega⟩
  let i : Fin 16 := ⟨n.val % 16, Nat.mod_lt _ (by decide)⟩
  have h := generatedTenth_packed_boundary_abs_max _ 144 (hb.2.1 g j a) i
  rw [generatedTenth_packed_boundary_stage_digit,
    generatedTenth_packed_boundary_prefix_recover] at h
  exact h

/-- The original last-pair word maxima bound every actual source coefficient. -/
theorem generatedTenth_packed_boundary_last_abs (hb : GeneratedTenthPackedBoundaryBounds)
    (g : Fin 2) (n : Fin 4096) (j : Fin 24) :
    |generatedTenthTwoFixerTensorState g (generatedTenthTwoFixerTensorPairs g).length n j| ≤
      176 := by
  let a : Fin 256 := ⟨n.val / 16, by omega⟩
  let i : Fin 16 := ⟨n.val % 16, Nat.mod_lt _ (by decide)⟩
  have h := generatedTenth_packed_boundary_abs_max _ 176 (hb.2.2 g j a) i
  rw [generatedTenth_packed_boundary_stage_digit,
    generatedTenth_packed_boundary_prefix_recover] at h
  exact h

/-- Actual inverse right labels and quadratic signs preserve the complete input bound. -/
theorem generatedTenth_packed_boundary_pre_abs (hb : GeneratedTenthPackedBoundaryBounds)
    (g : Fin 2) (k : Fin 24) (n : Fin 4096) :
    |generatedTenthTwoFixerTensorPreInteger g
      (fun m => generatedTenthTwoFixerTensorInput m k) n| ≤ 176 := by
  unfold generatedTenthTwoFixerTensorPreInteger
  rw [abs_mul, sign_abs, one_mul]
  exact generatedTenth_packed_boundary_input_abs hb _ k

/-- Actual inverse left labels and both full central/quadratic signs preserve the complete bound. -/
theorem generatedTenth_packed_boundary_post_abs (hb : GeneratedTenthPackedBoundaryBounds)
    (g : Fin 2) (j : Fin 24) (n : Fin 4096) :
    |generatedTenthTwoFixerTensorPostInteger g
      (fun m => generatedTenthTwoFixerTensorState g (generatedTenthTwoFixerTensorPairs g).length
        m j) n| ≤ 176 := by
  unfold generatedTenthTwoFixerTensorPostInteger
  simp only [abs_mul, sign_abs, one_mul]
  exact generatedTenth_packed_boundary_last_abs hb g _ j

/-- All sixteen pre slots are bound to the genuine original inverse-label and phase evaluation. -/
theorem generatedTenth_packed_boundary_pre_digit (hb : GeneratedTenthPackedBoundaryBounds)
    (g : Fin 2) (k : Fin 24) (a : Fin 256) (i : Fin 16) :
    generatedRootEightPackedSignedDigit (generatedTenthPackedBoundaryPreWord g k a) i =
      generatedTenthTwoFixerTensorPreInteger g
        (fun m => generatedTenthTwoFixerTensorInput m k)
        (generatedNinthLowerSpinPackedPrefixIndex a i) :=
  generatedTenth_packed_boundary_word_digit _
    (fun _s => generatedTenth_packed_boundary_pre_abs hb g k _) i

/-- All sixteen post slots keep the actual central Pauli field and first quadratic phase. -/
theorem generatedTenth_packed_boundary_post_digit (hb : GeneratedTenthPackedBoundaryBounds)
    (g : Fin 2) (j : Fin 24) (a : Fin 256) (i : Fin 16) :
    generatedRootEightPackedSignedDigit (generatedTenthPackedBoundaryPostWord g j a) i =
      generatedTenthTwoFixerTensorPostInteger g
        (fun m => generatedTenthTwoFixerTensorState g (generatedTenthTwoFixerTensorPairs g).length
          m j) (generatedNinthLowerSpinPackedPrefixIndex a i) :=
  generatedTenth_packed_boundary_word_digit _
    (fun _s => generatedTenth_packed_boundary_post_abs hb g j _) i

private theorem input_eight (n : Fin 4096) (j : Fin 24) :
    (8 : ℤ) ∣ generatedTenthTwoFixerTensorInput n j := by
  let a : Fin 256 := ⟨n.val / 16, by omega⟩
  let i : Fin 16 := ⟨n.val % 16, Nat.mod_lt _ (by decide)⟩
  have h := generatedRootEight_packed_signed_digit_eight _
    (generatedTenth_packed_boundary_input_width_gap j a).2 i
  rw [generatedTenth_packed_boundary_input_digit,
    generatedTenth_packed_boundary_prefix_recover] at h
  exact h

private theorem last_eight (g : Fin 2) (n : Fin 4096) (j : Fin 24) :
    (8 : ℤ) ∣ generatedTenthTwoFixerTensorState g
      (generatedTenthTwoFixerTensorPairs g).length n j := by
  let a : Fin 256 := ⟨n.val / 16, by omega⟩
  let i : Fin 16 := ⟨n.val % 16, Nat.mod_lt _ (by decide)⟩
  have h := generatedRootEight_packed_signed_digit_eight _
    (generatedTenth_packed_boundary_last_width_gap g j a).2 i
  rw [generatedTenth_packed_boundary_stage_digit,
    generatedTenth_packed_boundary_prefix_recover] at h
  exact h

private theorem pre_eight (g : Fin 2) (k : Fin 24) (n : Fin 4096) :
    (8 : ℤ) ∣ generatedTenthTwoFixerTensorPreInteger g
      (fun m => generatedTenthTwoFixerTensorInput m k) n := by
  unfold generatedTenthTwoFixerTensorPreInteger
  exact dvd_mul_of_dvd_right (input_eight _ k) _

private theorem post_eight (g : Fin 2) (j : Fin 24) (n : Fin 4096) :
    (8 : ℤ) ∣ generatedTenthTwoFixerTensorPostInteger g
      (fun m => generatedTenthTwoFixerTensorState g (generatedTenthTwoFixerTensorPairs g).length
        m j) n := by
  unfold generatedTenthTwoFixerTensorPostInteger
  exact dvd_mul_of_dvd_right (last_eight g _ j) _

private theorem weighted_abs {n : ℕ} (c v : Fin n → ℤ) (M : ℤ)
    (hv : ∀ k, |v k| ≤ M) : |∑ k, c k * v k| ≤ (∑ k, |c k|) * M := by
  calc
    _ ≤ ∑ k, |c k * v k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, |c k| * M := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hv k) (abs_nonneg _)
    _ = _ := (Finset.sum_mul _ _ _).symm

private theorem pre_physical_sum (g : Fin 2) (j : Fin 24) (n : Fin 4096) :
    generatedTenthTwoFixerTensorPreInteger g
      (fun m => generatedTenthTwoFixerTensorSpatialInteger g m j) n =
        ∑ k : Fin 24, generatedTenthTwoFixerTensorNumerator g j k *
          generatedTenthTwoFixerTensorPreInteger g
            (fun m => generatedTenthTwoFixerTensorInput m k) n := by
  unfold generatedTenthTwoFixerTensorPreInteger generatedTenthTwoFixerTensorSpatialInteger
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

set_option maxHeartbeats 2000000 in
-- The complete sixteen-slot uniqueness transport includes all signed coefficients.
/-- Full weighted Start word equations imply every original coordinate, with actual denominator4. -/
theorem generatedTenth_packed_boundary_start_actual (hb : GeneratedTenthPackedBoundaryBounds)
    (hw : GeneratedTenthPackedBoundaryStartWords) :
    GeneratedTenthTwoFixerTensorStartCondition := by
  intro g j n
  let a : Fin 256 := ⟨n.val / 16, by omega⟩
  let i : Fin 16 := ⟨n.val % 16, Nat.mod_lt _ (by decide)⟩
  have hd := (generatedTenth_packed_boundary_row_budget g j).1
  have hrow := (generatedTenth_packed_boundary_row_budget g j).2
  have he := generatedRootEight_packed_signed_linear
    (fun k : Fin 24 => generatedTenthPackedBoundaryPreWord g k a)
    (generatedTenthPackedBoundaryStageWord g 0 j a)
    (generatedTenthTwoFixerTensorNumerator g j)
    (generatedTenthTwoFixerTensorDenominator g : ℤ) 8 (by norm_num)
    (fun _ => generatedTenth_packed_boundary_word_lt _)
    (generatedTenth_packed_boundary_zero_width_gap g j a).1
    (fun s => by
      apply dvd_sub
      · apply Finset.dvd_sum
        intro k _
        rw [generatedTenth_packed_boundary_pre_digit hb]
        exact dvd_mul_of_dvd_right (pre_eight g k _) _
      · exact dvd_mul_of_dvd_right (generatedRootEight_packed_signed_digit_eight _
          (generatedTenth_packed_boundary_zero_width_gap g j a).2 s) _)
    (fun s => by
      have hs := weighted_abs (generatedTenthTwoFixerTensorNumerator g j)
        (fun k => generatedRootEightPackedSignedDigit
          (generatedTenthPackedBoundaryPreWord g k a) s) 176 (fun k => by
            rw [generatedTenth_packed_boundary_pre_digit hb]
            exact generatedTenth_packed_boundary_pre_abs hb g k _)
      have ht := generatedTenth_packed_boundary_abs_max _ 144 (hb.2.1 g j a) s
      have hx := abs_sub_le
        (∑ k : Fin 24, generatedTenthTwoFixerTensorNumerator g j k *
          generatedRootEightPackedSignedDigit (generatedTenthPackedBoundaryPreWord g k a) s)
        0 ((generatedTenthTwoFixerTensorDenominator g : ℤ) *
          generatedRootEightPackedSignedDigit (generatedTenthPackedBoundaryStageWord g 0 j a) s)
      simp only [sub_zero, zero_sub, abs_neg] at hx
      rw [hd, abs_mul] at hx
      rw [hd]
      norm_num at ht hs hrow hx ⊢
      nlinarith)
    (hw g j a)
  have hi := he i
  simp only [generatedTenth_packed_boundary_pre_digit hb,
    generatedTenth_packed_boundary_stage_digit] at hi
  rw [show generatedNinthLowerSpinPackedPrefixIndex a i = n from
    generatedTenth_packed_boundary_prefix_recover n] at hi
  exact hi.symm.trans (pre_physical_sum g j n).symm

set_option maxHeartbeats 2000000 in
-- The complete sixteen-slot uniqueness transport includes all signed coefficients.
/-- Complete original post word and final cache equations imply both full4096-coordinate clauses. -/
theorem generatedTenth_packed_boundary_finish_actual (hb : GeneratedTenthPackedBoundaryBounds)
    (hw : GeneratedTenthPackedBoundaryFinishWords) :
    GeneratedTenthTwoFixerTensorFinishCondition := by
  intro g j n
  let a : Fin 256 := ⟨n.val / 16, by omega⟩
  let i : Fin 16 := ⟨n.val % 16, Nat.mod_lt _ (by decide)⟩
  have he := generatedRootEight_packed_signed_linear
    (fun _ : Fin 1 => generatedTenthPackedBoundaryPostWord g j a)
    (generatedTenthPackedBoundaryInputWord j a) (fun _ => (1 : ℤ)) 1 8 (by norm_num)
    (fun _ => generatedTenth_packed_boundary_word_lt _)
    (generatedTenth_packed_boundary_input_width_gap j a).1
    (fun s => by
      simp only [Fin.sum_univ_one, one_mul]
      apply dvd_sub
      · rw [generatedTenth_packed_boundary_post_digit hb]
        exact post_eight g j _
      · exact generatedRootEight_packed_signed_digit_eight _
          (generatedTenth_packed_boundary_input_width_gap j a).2 s)
    (fun s => by
      simp only [Fin.sum_univ_one, one_mul]
      have hs := generatedTenth_packed_boundary_post_abs hb g j
        (generatedNinthLowerSpinPackedPrefixIndex a s)
      rw [← generatedTenth_packed_boundary_post_digit hb g j a s] at hs
      have ht := generatedTenth_packed_boundary_abs_max _ 176 (hb.1 j a) s
      have hx := abs_sub_le
        (generatedRootEightPackedSignedDigit (generatedTenthPackedBoundaryPostWord g j a) s)
        0 (generatedRootEightPackedSignedDigit (generatedTenthPackedBoundaryInputWord j a) s)
      simp only [sub_zero, zero_sub, abs_neg] at hx
      norm_num at ht hs hx ⊢
      linarith)
    (by simpa using (hw g j a).1)
  have hi := he i
  simp only [Fin.sum_univ_one, one_mul, generatedTenth_packed_boundary_post_digit hb,
    generatedTenth_packed_boundary_input_digit] at hi
  rw [show generatedNinthLowerSpinPackedPrefixIndex a i = n from
    generatedTenth_packed_boundary_prefix_recover n] at hi
  have hf := congrArg (fun w => generatedRootEightPackedSignedDigit w i) (hw g j a).2
  simp only [generatedTenth_packed_boundary_stage_digit,
    generatedTenth_packed_boundary_input_digit] at hf
  rw [show generatedNinthLowerSpinPackedPrefixIndex a i = n from
    generatedTenth_packed_boundary_prefix_recover n] at hf
  exact ⟨hi.trans hf.symm, hf⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
