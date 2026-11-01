/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The symmetric spatial coefficient in the nonzero XYZ cubic. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityPairShort

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The spatial cubic coefficient depends only on coincidences among the three positions. -/
noncomputable def trialityXYZSpatial (j k l : Fin 24) : ℝ :=
  (-1 + 4 * ((if j = k then 1 else 0) + (if j = l then 1 else 0) +
    (if k = l then 1 else 0)) - 16 * (if j = k ∧ k = l then 1 else 0)) / 4

theorem trialityXYZSpatial_cycle (j k l : Fin 24) :
    trialityXYZSpatial j k l = trialityXYZSpatial l j k := by
  by_cases hjk : j = k <;> by_cases hjl : j = l <;> by_cases hkl : k = l <;>
    simp_all [trialityXYZSpatial, eq_comm]

/-- The actual odd-short tensor coefficient is the spatial cubic coefficient times code signs. -/
theorem conwayTensorCoefficient_odd_spatial (d : Fin 2048) (j k l : Fin 24) :
    conwayTensorCoefficient (Sum.inr (Sum.inr (d,j))) k l =
      (if (golayEncodedMask d.val).testBit k.val then -1 else 1) *
      (if (golayEncodedMask d.val).testBit l.val then -1 else 1) *
        trialityXYZSpatial j k l := by
  unfold conwayTensorCoefficient
  rw [griessShortVector_X_coordinate, griessShortVector_X_coordinate,
    mul_assoc (2 : ℝ), div_mul_div_comm]
  rw [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 8)]
  by_cases hjk : j = k
  · subst k
    by_cases hjl : j = l
    · subst l
      cases h : (golayEncodedMask d.val).testBit j.val <;>
        simp [trialityXYZSpatial] <;> ring
    · cases hj : (golayEncodedMask d.val).testBit j.val <;>
        cases hl : (golayEncodedMask d.val).testBit l.val <;>
          simp [trialityXYZSpatial, hjl, (Ne.symm hjl)] <;> ring
  · by_cases hjl : j = l
    · subst l
      cases hj : (golayEncodedMask d.val).testBit j.val <;>
        cases hk : (golayEncodedMask d.val).testBit k.val <;>
          simp [trialityXYZSpatial, hjk, (Ne.symm hjk)] <;> ring
    · by_cases hkl : k = l
      · subst l
        cases hk : (golayEncodedMask d.val).testBit k.val <;>
          simp [trialityXYZSpatial, hjk, (Ne.symm hjk)] <;> ring
      · cases hk : (golayEncodedMask d.val).testBit k.val <;>
          cases hl : (golayEncodedMask d.val).testBit l.val <;>
            simp [trialityXYZSpatial, hjk, (Ne.symm hjk), hjl, (Ne.symm hjl), hkl] <;> ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
