/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7StandardNormLine

/-! Every complete actual signed flag candidate fixes the entire original norm-twelve line. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original signed coordinate formula holds for every whole candidate isometry. -/
theorem generatedTenth_e7_signed_flag_line_coordinate
    (v : generatedTenthE7SignedFlagCandidates) (i : Fin 24) :
    (leechIntegralAction (generatedTenthE7SignedFlagSpatial v)
      generatedTenthE7StandardNormTwelveLine).val i =
      if v.2.val.val i = 0 then generatedTenthE7XiLine (v.1.val.val.val.symm i)
        else -generatedTenthE7XiLine (v.1.val.val.val.symm i) := by
  unfold generatedTenthE7SignedFlagSpatial golayMonomialPair
  rw [map_mul, LinearEquiv.mul_apply, leechIntegralAction_golaySign,
    leechIntegralAction_golayPermutation, generatedTenth_e7_standard_norm_line_source]
  rfl

/-- The exact complete phase correction gives one common orientation
on the whole outside support. -/
theorem generatedTenth_e7_signed_flag_line_phase
    (v : generatedTenthE7SignedFlagCandidates) (i : Fin 6) :
    v.2.val.val (generatedTenthE7StandardOutsideCoordinates i) +
      generatedTenthE7StandardOutsideSigns
        ((generatedTenthE7StandardOutsidePermutation v.1).symm i) =
      (v.2.val.val 14 + generatedTenthE7SignedFlagPhase v.1 0) +
        generatedTenthE7StandardOutsideSigns i := by
  have h := v.2.property.2 i
  change v.2.val.val (generatedTenthE7StandardOutsideCoordinates i) +
    (generatedTenthE7StandardOutsideSigns i + generatedTenthE7StandardOutsideSigns
      ((generatedTenthE7StandardOutsidePermutation v.1).symm i)) = _ at h
  calc
    _ = (v.2.val.val (generatedTenthE7StandardOutsideCoordinates i) +
      (generatedTenthE7StandardOutsideSigns i + generatedTenthE7StandardOutsideSigns
        ((generatedTenthE7StandardOutsidePermutation v.1).symm i))) +
          generatedTenthE7StandardOutsideSigns i := by
      have hz := ZModModule.add_self (generatedTenthE7StandardOutsideSigns i)
      calc
        _ = (v.2.val.val (generatedTenthE7StandardOutsideCoordinates i) +
          generatedTenthE7StandardOutsideSigns
            ((generatedTenthE7StandardOutsidePermutation v.1).symm i)) +
              (generatedTenthE7StandardOutsideSigns i +
                generatedTenthE7StandardOutsideSigns i) := by rw [hz, add_zero]
        _ = _ := by abel
    _ = _ := by rw [h]

/-- The entire actual source vector is multiplied by one common original integer sign. -/
theorem generatedTenth_e7_signed_flag_line_orientation
    (v : generatedTenthE7SignedFlagCandidates) :
    leechIntegralAction (generatedTenthE7SignedFlagSpatial v)
        generatedTenthE7StandardNormTwelveLine =
      generatedTenthE7IntegerSign
        (v.2.val.val 14 + generatedTenthE7SignedFlagPhase v.1 0) •
          generatedTenthE7StandardNormTwelveLine := by
  apply Subtype.ext
  funext i
  rw [generatedTenth_e7_signed_flag_line_coordinate]
  change _ = generatedTenthE7IntegerSign
    (v.2.val.val 14 + generatedTenthE7SignedFlagPhase v.1 0) *
      generatedTenthE7StandardNormTwelveLine.val i
  rw [generatedTenth_e7_standard_norm_line_source]
  by_cases hi : generatedTenthE7StandardOutside i
  · obtain ⟨j, hj⟩ := generatedTenthE7StandardOutsideEquiv.surjective ⟨i, hi⟩
    have hji : generatedTenthE7StandardOutsideCoordinates j = i := congrArg Subtype.val hj
    rw [← hji]
    have hpre : v.1.val.val.val.symm (generatedTenthE7StandardOutsideCoordinates j) =
        generatedTenthE7StandardOutsideCoordinates
          ((generatedTenthE7StandardOutsidePermutation v.1).symm j) := by
      have h := generatedTenth_e7_standard_outside_permutation_coordinate v.1
        ((generatedTenthE7StandardOutsidePermutation v.1).symm j)
      rw [Equiv.apply_symm_apply] at h
      exact (v.1.val.val.val.symm_apply_eq).mpr h
    rw [hpre, generatedTenth_e7_standard_norm_line_sign,
      generatedTenth_e7_standard_norm_line_sign]
    exact (generatedTenth_e7_four_sign_phase _ _ _ _).mpr
      (generatedTenth_e7_signed_flag_line_phase v j)
  · have hz : generatedTenthE7XiLine i = 0 := by
      by_contra hz
      exact hi ((generatedTenth_e7_standard_norm_line_nonzero i).mp hz)
    have hpre : ¬ generatedTenthE7StandardOutside (v.1.val.val.val.symm i) := by
      intro hp
      have h := (generatedTenth_e7_standard_flag_outside v.1
        (v.1.val.val.val.symm i)).mpr hp
      rw [v.1.val.val.val.apply_symm_apply] at h
      exact hi h
    have hpz : generatedTenthE7XiLine (v.1.val.val.val.symm i) = 0 := by
      by_contra hpz
      exact hpre ((generatedTenth_e7_standard_norm_line_nonzero _).mp hpz)
    rw [hz, hpz]
    simp

/-- Every actual candidate preserves the complete original norm-twelve vector up to sign. -/
theorem generatedTenth_e7_signed_flag_line_fix (v : generatedTenthE7SignedFlagCandidates) :
    leechIntegralAction (generatedTenthE7SignedFlagSpatial v)
      generatedTenthE7StandardNormTwelveLine = generatedTenthE7StandardNormTwelveLine ∨
    leechIntegralAction (generatedTenthE7SignedFlagSpatial v)
      generatedTenthE7StandardNormTwelveLine = -generatedTenthE7StandardNormTwelveLine := by
  rw [generatedTenth_e7_signed_flag_line_orientation]
  by_cases h : v.2.val.val 14 + generatedTenthE7SignedFlagPhase v.1 0 = 0
  · exact Or.inl (by simp [generatedTenthE7IntegerSign, h])
  · exact Or.inr (by simp [generatedTenthE7IntegerSign, h])

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
