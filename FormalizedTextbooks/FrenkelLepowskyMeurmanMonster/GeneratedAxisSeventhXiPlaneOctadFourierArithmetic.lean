/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneOctadSparseCoefficients
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityOrder

/-! Every outgoing octad coefficient retains the complete original sixty-four-row Fourier sum. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- An absent sign slot has zero coefficient; every occupied sign is an actual finite label. -/
theorem generatedSeventhXiOctad_sign_or_zero (g : Fin 231) (k : Fin 3) :
    generatedSeventhXiOctadSigns g k < 64 ∨ generatedSeventhXiOctadWeights g k = 0 := by
  have h := generatedSeventhXiOctad_entry g k
  by_cases hv : generatedSeventhXiOctadEntries g k < 552
  · rw [dite_eq_left hv] at h
    dsimp only at h
    have hb := (generatedSeventhXiShort_octad_data _ _ h.2.2.1).2.2.1
    rw [← h.2.2.2.2.1] at hb
    exact Or.inl hb
  · rw [dite_eq_right hv] at h
    exact Or.inr h.2

/-- The complete outgoing integer numerator from the original three signed incoming slots. -/
def generatedSeventhXiOctadFourierNumerator (g : Fin 231) (e : Fin 64) : ℤ :=
  ∑ k : Fin 3, generatedSeventhXiOctadWeights g k *
    trialityIntegerMatrix e
      ⟨generatedSeventhXiOctadSigns g k % 64, Nat.mod_lt _ (by decide)⟩

private theorem row_fourier (c : Fin 4096) (e : Fin 64) (g : Fin 231) (k : Fin 3) :
    (∑ f : Fin 64, trialityIntegerMatrix e f *
      generatedSeventhXiOctadRowCoefficient c f g k) =
      generatedSeventhXiOctadWeights g k *
        trialityIntegerMatrix e
          ⟨generatedSeventhXiOctadSigns g k % 64, Nat.mod_lt _ (by decide)⟩ *
        (if generatedSeventhXiOctadCodes g = c.val then 1 else 0) := by
  by_cases hc : generatedSeventhXiOctadCodes g = c.val
  · obtain hb | hz := generatedSeventhXiOctad_sign_or_zero g k
    · let s : Fin 64 := ⟨generatedSeventhXiOctadSigns g k % 64, Nat.mod_lt _ (by decide)⟩
      have he (f : Fin 64) : generatedSeventhXiOctadSigns g k = f.val ↔ f = s := by
        rw [Fin.ext_iff]
        change generatedSeventhXiOctadSigns g k = f.val ↔
          f.val = generatedSeventhXiOctadSigns g k % 64
        rw [Nat.mod_eq_of_lt hb]
        exact eq_comm
      simp only [generatedSeventhXiOctadRowCoefficient, hc, true_and, he,
        ite_true, mul_one]
      have ht (f : Fin 64) : trialityIntegerMatrix e f *
          (generatedSeventhXiOctadWeights g k * (if f = s then 1 else 0)) =
          if f = s then generatedSeventhXiOctadWeights g k * trialityIntegerMatrix e s
          else 0 := by
        split_ifs with h
        · subst f
          ring
        · ring
      simp only [ht, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rfl
    · simp [generatedSeventhXiOctadRowCoefficient, hz]
  · simp [generatedSeventhXiOctadRowCoefficient, hc]

/-- The complete source Fourier sum equals the exact three-slot family sum, including all phases. -/
theorem generatedSeventhXiOctad_fourier_sum (c : Fin 4096) (e : Fin 64) :
    (∑ f : Fin 64, trialityIntegerMatrix e f * generatedSeventhXiMiddleOctadNumerator c f) =
      ∑ g : Fin 231, generatedSeventhXiOctadFourierNumerator g e *
        (if generatedSeventhXiOctadCodes g = c.val then 1 else 0) := by
  simp_rw [generatedSeventhXiOctad_sparse_coefficient, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  rw [Finset.sum_comm]
  simp only [row_fourier, generatedSeventhXiOctadFourierNumerator, Finset.sum_mul]

/-- The original real octad operator has the exact integer numerator divided by thirty-two. -/
theorem generatedSeventhXi_canonical_octad_fourier (o : Fin 759) (e : Fin 64) :
    (griessConwayEncode generatedSeventhXiPlaneCanonicalAxis).2.1
      (Sum.inr (Sum.inl (o, e))) =
      ((∑ g : Fin 231, generatedSeventhXiOctadFourierNumerator g e *
        (if generatedSeventhXiOctadCodes g = (golayOctadLabel o).val then 1 else 0) : ℤ) : ℝ) /
        32 := by
  rw [generatedSeventhXi_canonical_axis_octad]
  simp_rw [← generatedSeventhXiMiddleOctadNumerator_eq]
  rw [trialityOctadAction_matrix]
  change (∑ f : Fin 64, ((1 / 8 : ℝ) * (trialityIntegerMatrix e f : ℝ)) *
    ((generatedSeventhXiMiddleOctadNumerator (golayOctadLabel o) f : ℝ) / 4)) = _
  have ht (f : Fin 64) : ((1 / 8 : ℝ) * (trialityIntegerMatrix e f : ℝ)) *
      ((generatedSeventhXiMiddleOctadNumerator (golayOctadLabel o) f : ℝ) / 4) =
      ((trialityIntegerMatrix e f *
        generatedSeventhXiMiddleOctadNumerator (golayOctadLabel o) f : ℤ) : ℝ) / 32 := by
    push_cast
    ring
  simp_rw [ht]
  rw [← Finset.sum_div, ← Int.cast_sum, generatedSeventhXiOctad_fourier_sum]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
