/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthTensorParity

/-! Complete original tensor candidate images detect every original Q fixation. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Excluding the genuine anti-Omega element from all32 original candidate images prevents
  fixation. -/
theorem generatedTenth_tensor_Q_not_fixed_of_images (k : Fin 14) (q₀ : Q)
    (hImages : ∀ b : ZMod 2, ∀ j : Fin 16,
      generatedTenthQWordImage k 7 (generatedFifthQCandidate b j) ≠
        q₀) :
    localTensorRepresentation (localFiberIncl q₀)
      (griessConwayEncode (rhoLocal (generatedAxisGlobalFifthShortLocalWord k)
        generatedFifthAxis)).2.2 ≠
      (griessConwayEncode (rhoLocal (generatedAxisGlobalFifthShortLocalWord k)
        generatedFifthAxis)).2.2 := by
  let f := generatedTenthQWordFiber k
  have hT : (griessConwayEncode (rhoLocal (generatedAxisGlobalFifthShortLocalWord k)
      generatedFifthAxis)).2.2 =
      localTensorRepresentation f (griessConwayEncode generatedFifthAxis).2.2 := by
    rw [← generatedTenth_Q_word_fiber_local]
    exact generatedFourth_local_tensor f generatedFifthAxis
  intro hfix
  rw [hT] at hfix
  obtain ⟨q, hq⟩ := (spinConjugation f.val.1).surjective q₀
  have hqT : localTensorRepresentation (localFiberIncl q)
      (griessConwayEncode generatedFifthAxis).2.2 =
      (griessConwayEncode generatedFifthAxis).2.2 := by
    apply (localTensorRepresentation f).injective
    rw [generatedAxisGlobalTensor_Q_intertwine, hq]
    exact hfix
  have hm : q ∈ generatedFifthTensorQStabilizer := by
    intro i
    funext t
    have h := congrArg (fun T : SpinIndex → Fin 24 → ℝ => T t i) hqT
    simpa only [localTensorRepresentation_q] using h
  obtain ⟨b, j, hj⟩ := (generatedFifth_tensor_Q_mem_iff q).mp hm
  apply hImages b j
  rw [hj, ← generatedTenth_Q_word_image]
  exact hq

/-- Identically zero outgoing tensor implies that the original incoming tensor is Omega invariant.
-/
theorem generatedTenth_tensor_Omega_fixed_of_outgoing_zero (x : GriessSpace)
    (hOut : (griessConwayEncode (sExtra x)).2.2 = 0) :
    localTensorRepresentation (localFiberIncl sourceOmegaQ)
      (griessConwayEncode x).2.2 = (griessConwayEncode x).2.2 := by
  have hl (d : Fin 2048) (i : Fin 24) :
      (griessConwayEncode x).2.2 (golayLabelCoefficients ⟨d.val, by omega⟩) i =
        (griessConwayEncode x).2.2 (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) i := by
    have h0 := congrArg (fun T : SpinIndex → Fin 24 → ℝ =>
      T (golayLabelCoefficients ⟨d.val, by omega⟩) i) hOut
    have h1 := congrArg (fun T : SpinIndex → Fin 24 → ℝ =>
      T (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) i) hOut
    rw [generatedSixth_triality_tensor_coordinate] at h0 h1
    simp only [spinDictionaryCode_low, spinDictionaryCode_high, trialityYTensor,
      golayLabel_low_last, golayLabel_high_last, qSign_zero, qSign_one, ite_true,
      one_mul, mul_one, Pi.zero_apply] at h0 h1
    have hp : qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) ≠ 0 := by
      intro hz
      have hh := qSign_sq (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ)
      rw [hz] at hh
      norm_num at hh
    have hs : (if (golayEncodedMask d.val).testBit i.val then (-1 : ℝ) else 1) ≠ 0 := by
      split_ifs <;> norm_num
    have hmul : qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
        (if (golayEncodedMask d.val).testBit i.val then (-1 : ℝ) else 1) *
        ((griessConwayEncode x).2.2 (golayLabelCoefficients ⟨d.val, by omega⟩) i -
          (griessConwayEncode x).2.2 (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) i) = 0 := by
      linear_combination h0 + h1
    exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left (mul_ne_zero hp hs))
  funext t i
  rw [localTensorRepresentation_q, sourceOmegaQ_spin]
  rcases spinDictionaryIndex_cases t with h | h
  · rw [h, golayLabel_low_add_omega]
    exact (hl _ i).symm
  · rw [h, golayLabel_high_add_omega]
    exact hl _ i

/-- Excluding Omega from all actual original candidate images proves a nonzero entire outgoing
  tensor. -/
theorem generatedTenth_tensor_nonzero_of_candidate_images (k : Fin 14)
    (hImages : ∀ b : ZMod 2, ∀ j : Fin 16,
      generatedTenthQWordImage k 7 (generatedFifthQCandidate b j) ≠ sourceOmegaQ) :
    (griessConwayEncode
      (sExtra (rhoLocal (generatedAxisGlobalFifthShortLocalWord k)
        generatedFifthAxis))).2.2 ≠ 0 := by
  intro hz
  exact generatedTenth_tensor_Q_not_fixed_of_images k sourceOmegaQ hImages
    (generatedTenth_tensor_Omega_fixed_of_outgoing_zero _ hz)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
