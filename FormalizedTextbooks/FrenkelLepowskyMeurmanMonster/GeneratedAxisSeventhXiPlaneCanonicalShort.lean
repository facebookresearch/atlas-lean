/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneCanonicalCoordinates

/-! Complete positive-triality pair and octad coordinates of the canonical seventh axis. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

private theorem pair_triality_raw (a : ConwayRawSpace) (s : Fin 2) (p : Fin 276) :
    (griessConwayEncode (sExtra (griessConwayDecode a))).2.1 (Sum.inl (s, p)) =
      (a.2.1 (Sum.inl (0, p)) - a.2.1 (Sum.inl (1, p))) / 2 +
        (if s = 0 then a.1 (griessCoordinatePair p).1 (griessCoordinatePair p).2
         else -a.1 (griessCoordinatePair p).1 (griessCoordinatePair p).2) := by
  have h1 : trialityCycle.symm 1 = 0 := by decide
  have h2 : trialityCycle.symm 2 = 1 := by decide
  fin_cases s <;>
    simp [griessConwayEncode, sExtra, griessTriality, griessConwayDecode,
      trialityBlockAction, trialityCycleAction, h1, h2] <;> ring

/-- Positive triality mixes both original preferred pair coefficients and the matrix entry. -/
theorem generatedSeventhXi_pair_triality_coordinate (x : GriessSpace) (s : Fin 2)
    (p : Fin 276) :
    (griessConwayEncode (sExtra x)).2.1 (Sum.inl (s, p)) =
      ((griessConwayEncode x).2.1 (Sum.inl (0, p)) -
        (griessConwayEncode x).2.1 (Sum.inl (1, p))) / 2 +
        (if s = 0 then (griessConwayEncode x).1
            (griessCoordinatePair p).1 (griessCoordinatePair p).2
         else -(griessConwayEncode x).1
            (griessCoordinatePair p).1 (griessCoordinatePair p).2) := by
  simpa only [griessConwayDecode_encode] using pair_triality_raw (griessConwayEncode x) s p

/-- Each canonical middle matrix entry has its genuine integer norm-eight numerator. -/
theorem generatedSeventhXi_canonical_middle_matrix (i j : Fin 24) :
    (griessConwayEncode generatedSeventhXiPlaneCanonicalMiddle).1 i j =
      ((if i = j then (8 : ℝ) else 0) +
        (generatedSeventhNormEightVectorData 7 i : ℝ) *
          (generatedSeventhNormEightVectorData 7 j : ℝ)) / 32 := by
  rw [generatedSeventhXiPlaneCanonicalMiddle_encode]
  change (griessConwayEncode
    (rhoLocal (localFiberIntoH generatedSeventhLocalFiber) generatedOddAxis)).1 i j = _
  rw [generatedSeventh_middle_matrix]
  have hv (k : Fin 24) : generatedNormEightVector generatedSeventhNormEightVector k =
      (generatedSeventhNormEightVectorData 7 k : ℝ) / Real.sqrt 8 := by
    simp only [generatedNormEightVector, generatedSeventhNormEightVector_val,
      leechCoordinateEmbedding]
    rfl
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    generatedNormEightLineMatrix, Matrix.vecMulVec_apply, Matrix.one_apply]
  rw [hv, hv]
  have hs : Real.sqrt 8 ≠ 0 := by positivity
  have hr : (Real.sqrt 8) ^ 2 = 8 := Real.sq_sqrt (by norm_num)
  split_ifs <;> field_simp [hs] <;> rw [hr] <;> ring

/-- Every outgoing pair row has an exact integer numerator divided by thirty-two. -/
theorem generatedSeventhXi_canonical_axis_pair (s : Fin 2) (p : Fin 276) :
    (griessConwayEncode generatedSeventhXiPlaneCanonicalAxis).2.1 (Sum.inl (s, p)) =
      (4 * ((generatedSeventhXiMiddleShortNumerator (Sum.inl (0, p)) : ℝ) -
          (generatedSeventhXiMiddleShortNumerator (Sum.inl (1, p)) : ℝ)) +
        (if s = 0 then 1 else -1) *
          (generatedSeventhNormEightVectorData 7 (griessCoordinatePair p).1 : ℝ) *
          (generatedSeventhNormEightVectorData 7 (griessCoordinatePair p).2 : ℝ)) / 32 := by
  rw [generatedSeventhXiPlaneCanonicalAxis, generatedSeventhXi_pair_triality_coordinate,
    generatedSeventhXi_canonical_middle_short, generatedSeventhXi_canonical_middle_short]
  have hn := griessCoordinatePair_ne p
  simp only [generatedSeventhXi_canonical_middle_matrix, hn, ite_false]
  split_ifs <;> ring

/-- Genuine positive triality applies its complete 64-row operator to each original octad family. -/
theorem generatedSeventhXi_octad_triality_coordinate (x : GriessSpace) (o : Fin 759)
    (e : Fin 64) :
    (griessConwayEncode (sExtra x)).2.1 (Sum.inr (Sum.inl (o, e))) =
      trialityOctadAction
        (fun f => (griessConwayEncode x).2.1 (Sum.inr (Sum.inl (o, f)))) e := by
  simp only [griessConwayEncode, sExtra, griessTriality, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, trialityBlockAction, LinearEquiv.prodCongr_apply]
  rfl

/-- Every outgoing octad row retains all sixty-four checked incoming central coefficients. -/
theorem generatedSeventhXi_canonical_axis_octad (o : Fin 759) (e : Fin 64) :
    (griessConwayEncode generatedSeventhXiPlaneCanonicalAxis).2.1
      (Sum.inr (Sum.inl (o, e))) =
      trialityOctadAction
        (fun f => (generatedSeventhXiMiddleShortNumerator (Sum.inr (Sum.inl (o, f))) : ℝ)
          / 4) e := by
  rw [generatedSeventhXiPlaneCanonicalAxis, generatedSeventhXi_octad_triality_coordinate]
  have he : (fun f => (griessConwayEncode generatedSeventhXiPlaneCanonicalMiddle).2.1
      (Sum.inr (Sum.inl (o, f)))) =
      (fun f => (generatedSeventhXiMiddleShortNumerator (Sum.inr (Sum.inl (o, f))) : ℝ)
        / 4) := by
    funext f
    exact generatedSeventhXi_canonical_middle_short _
  rw [he]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
