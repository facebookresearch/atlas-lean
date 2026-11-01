/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneMiddleShortSparse

/-! Exact quarter-integral weights of the complete original seventh middle short vector. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- The original odd-axis pair coefficient numerator is one or three with its actual pair sign. -/
def generatedSeventhXiShortInputWeight (s : Fin 2) (p : Fin 276) : ℤ :=
  (if s = 0 then 1 else -1) *
    (if (generatedSeventhXiShortInputCoordinates p).1 = 0 then -3 else 1)

/-- All original pair coefficients have their exact denominator-four normalization. -/
theorem generatedSeventhXiShortInput_weight (s : Fin 2) (p : Fin 276) :
    (griessConwayEncode generatedOddAxis).2.1 (generatedSeventhXiShortInputLabel s p) =
      (generatedSeventhXiShortInputWeight s p : ℝ) / 4 := by
  have hb : (generatedSeventhXiShortInputCoordinates p).2 ≠ 0 := by
    intro he
    have h := generatedSeventhXiShort_input_pairs.1 p
    rw [he] at h
    exact (Fin.not_lt_zero _) h
  have hg : golayEncodedMask 0 = 0 := by decide +kernel
  change (griessConwayEncode
    (sExtra (conwayShortAxis (Sum.inr (Sum.inr (0, 0))) 0))).2.1
      (Sum.inl (s, generatedSeventhXiShortInputIndex p)) = _
  rw [generatedAxis_triality_odd_pair_coordinate, generatedSeventhXiShortInputIndex_coordinates]
  have hs : Real.sqrt 8 ≠ 0 := by positivity
  have hroot : (Real.sqrt 8) ^ 2 = 8 := Real.sq_sqrt (by norm_num)
  norm_num [griessShortVector, griessShortIntegral, hg, hb, generatedSeventhXiShortInputWeight]
  split_ifs <;> field_simp [hs] <;> nlinarith [hroot]

/-- The genuine local quotient action has the entire checked signed, quarter-integral short sum. -/
theorem generatedSeventhXi_middle_short_weighted :
    (griessConwayEncode
      (rhoLocal (localFiberIntoH generatedSeventhLocalFiber) generatedOddAxis)).2.1 =
      ∑ s : Fin 2, ∑ p : Fin 276,
        ((generatedSeventhXiShortInputWeight s p : ℝ) / 4 *
          qSign (generatedSeventhXiShortPhaseBit s p : ZMod 2)) •
          Pi.single (generatedSeventhXiShortOutputLabel s p) (1 : ℝ) := by
  change (griessConwayEncode
    (localGriessRepresentation generatedSeventhLocalFiber generatedOddAxis)).2.1 = _
  rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply]
  change localShortRepresentation generatedSeventhLocalFiber
    (griessConwayEncode generatedOddAxis).2.1 = _
  rw [generatedSeventhXi_middle_short_expansion]
  simp_rw [generatedSeventhXiShortInput_weight]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
