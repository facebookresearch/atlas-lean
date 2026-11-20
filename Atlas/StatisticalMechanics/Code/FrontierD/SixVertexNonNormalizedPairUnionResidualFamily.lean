/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexPositiveUnitComponentResidualRouting
















namespace StatMech.FrontierD

noncomputable section

local instance nonNormalizedPairUnionResidualFamilyDecidableProp (p : Prop) :
    Decidable p := Classical.propDecidable p



abbrev SixVertexNonNormalizedUnitChargeResidualSources
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) :=
  {source : SixVertexPositiveUnitComponentResidualGeometricSources T middle
      hmiddle_pos hmiddle_lt grade //
    SixVertexLocallyDegreeTwo
      (sixVertexHorizontalActualDeficitConfigurationPair source.1).1.1.1
      (sixVertexHorizontalActualDeficitConfigurationPair source.1).1.2.1}



theorem SixVertexNonNormalizedUnitChargeResidualSources.unitCharge
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexNonNormalizedUnitChargeResidualSources T middle
      hmiddle_pos hmiddle_lt grade) :
    sixVertexHorizontalDegreeTwoUnitCharge source.1.1 :=
  sixVertexHorizontalDegreeTwoUnitCharge_of_not_highCharge source.1.1
    source.2 source.1.2.2






structure SixVertexNonNormalizedPairUnionPhysicalTargetFamily
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) where
  target :
    (SixVertexNonNormalizedUnitChargeResidualSources T middle
        hmiddle_pos hmiddle_lt grade × Bool) ↪
      {pair : SixVertexConfigurationPhysicalTarget T middle //
        sixVertexConfigurationPairBigrade pair = grade}
  related : ∀ source branch,
    SixVertexConfigurationPairTwoCycleFineRelated
      (sixVertexHorizontalActualDeficitConfigurationPair source.1.1).1
      (target (source, branch)).1
  oldSourceWeight_eq_zero : ∀ source branch,
    sixVertexHorizontalPairProfileChooseWeight
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt)
        (sixVertexHorizontalPairCompletionProfile T
          ((target (source, branch)).1.1.1.horizontal,
            (target (source, branch)).1.2.1.horizontal)) = 0

namespace SixVertexNonNormalizedPairUnionPhysicalTargetFamily

variable {T : EvenTorus} {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}



noncomputable def surplusTarget
    (family : SixVertexNonNormalizedPairUnionPhysicalTargetFamily T middle
      hmiddle_pos hmiddle_lt grade)
    (coded : SixVertexNonNormalizedUnitChargeResidualSources T middle
      hmiddle_pos hmiddle_lt grade × Bool) :
    SixVertexHorizontalDegreeTwoHallTarget T middle
      hmiddle_pos hmiddle_lt grade :=
  Classical.choose
    (sixVertexHorizontalActualSurplusConfigurationPair_surjective_of_horizontalSourceWeight_eq_zero
      (family.target coded)
      (family.oldSourceWeight_eq_zero coded.1 coded.2))


theorem surplusTarget_physical
    (family : SixVertexNonNormalizedPairUnionPhysicalTargetFamily T middle
      hmiddle_pos hmiddle_lt grade)
    (coded : SixVertexNonNormalizedUnitChargeResidualSources T middle
      hmiddle_pos hmiddle_lt grade × Bool) :
    sixVertexHorizontalActualSurplusConfigurationPair
        (family.surplusTarget coded) =
      family.target coded :=
  Classical.choose_spec
    (sixVertexHorizontalActualSurplusConfigurationPair_surjective_of_horizontalSourceWeight_eq_zero
      (family.target coded)
      (family.oldSourceWeight_eq_zero coded.1 coded.2))


noncomputable def surplusEmbedding
    (family : SixVertexNonNormalizedPairUnionPhysicalTargetFamily T middle
      hmiddle_pos hmiddle_lt grade) :
    (SixVertexNonNormalizedUnitChargeResidualSources T middle
        hmiddle_pos hmiddle_lt grade × Bool) ↪
      SixVertexHorizontalDegreeTwoHallTarget T middle
        hmiddle_pos hmiddle_lt grade where
  toFun := family.surplusTarget
  inj' := by
    intro first second heq
    apply family.target.injective
    rw [← family.surplusTarget_physical first,
      ← family.surplusTarget_physical second]
    exact congrArg sixVertexHorizontalActualSurplusConfigurationPair heq



noncomputable def decoder
    (family : SixVertexNonNormalizedPairUnionPhysicalTargetFamily T middle
      hmiddle_pos hmiddle_lt grade)
    (target : SixVertexHorizontalDegreeTwoHallTarget T middle
      hmiddle_pos hmiddle_lt grade) :
    Option (SixVertexHorizontalDegreeTwoHallSource T middle
      hmiddle_pos hmiddle_lt grade) :=
  if h : ∃ coded, family.surplusEmbedding coded = target then
    some (Classical.choose h).1.1.1
  else none



theorem decode_surplusTarget
    (family : SixVertexNonNormalizedPairUnionPhysicalTargetFamily T middle
      hmiddle_pos hmiddle_lt grade)
    (source : SixVertexNonNormalizedUnitChargeResidualSources T middle
      hmiddle_pos hmiddle_lt grade)
    (branch : Bool) :
    family.decoder (family.surplusTarget (source, branch)) =
      some source.1.1 := by
  let coded := (source, branch)
  have hexists : ∃ candidate,
      family.surplusEmbedding candidate = family.surplusTarget coded :=
    ⟨coded, rfl⟩
  rw [decoder, dif_pos hexists]
  have hchosen : Classical.choose hexists = coded := by
    apply family.surplusEmbedding.injective
    exact Classical.choose_spec hexists
  rw [hchosen]


theorem surplusTarget_supported
    (family : SixVertexNonNormalizedPairUnionPhysicalTargetFamily T middle
      hmiddle_pos hmiddle_lt grade)
    (source : SixVertexNonNormalizedUnitChargeResidualSources T middle
      hmiddle_pos hmiddle_lt grade)
    (branch : Bool) :
    sixVertexHorizontalOffDiagonalTwoCycleSupport T middle
      hmiddle_pos hmiddle_lt grade source.1.1
        (family.surplusTarget (source, branch)) := by
  change SixVertexConfigurationPairTwoCycleFineRelated
    (sixVertexHorizontalActualDeficitConfigurationPair source.1.1).1
    (sixVertexHorizontalActualSurplusConfigurationPair
      (family.surplusTarget (source, branch))).1
  rw [family.surplusTarget_physical]
  exact family.related source branch


theorem surplusTarget_joint_injective
    (family : SixVertexNonNormalizedPairUnionPhysicalTargetFamily T middle
      hmiddle_pos hmiddle_lt grade) :
    Function.Injective (fun coded => family.surplusTarget coded) :=
  family.surplusEmbedding.injective


theorem surplusTarget_branch_injective
    (family : SixVertexNonNormalizedPairUnionPhysicalTargetFamily T middle
      hmiddle_pos hmiddle_lt grade)
    (branch : Bool) :
    Function.Injective (fun source => family.surplusTarget (source, branch)) := by
  intro first second heq
  exact congrArg Prod.fst (family.surplusEmbedding.injective heq)



theorem surplusTarget_branches_disjoint
    (family : SixVertexNonNormalizedPairUnionPhysicalTargetFamily T middle
      hmiddle_pos hmiddle_lt grade)
    (first second : SixVertexNonNormalizedUnitChargeResidualSources T middle
      hmiddle_pos hmiddle_lt grade) :
    family.surplusTarget (first, false) ≠
      family.surplusTarget (second, true) := by
  intro heq
  have hcoded : (first, false) = (second, true) :=
    family.surplusEmbedding.injective heq
  exact Bool.false_ne_true (congrArg Prod.snd hcoded)



noncomputable def geometricRepair
    (family : SixVertexNonNormalizedPairUnionPhysicalTargetFamily T middle
      hmiddle_pos hmiddle_lt grade)
    (source : SixVertexNonNormalizedUnitChargeResidualSources T middle
      hmiddle_pos hmiddle_lt grade)
    (branch : Bool) :
    SixVertexHorizontalResidualGeometricSurplusRepair source.1.1 :=
  SixVertexHorizontalResidualGeometricSurplusRepair.ofFineRelated
    source.1.1 (family.surplusTarget (source, branch))
      (family.surplusTarget_supported source branch)

@[simp] theorem geometricRepair_target
    (family : SixVertexNonNormalizedPairUnionPhysicalTargetFamily T middle
      hmiddle_pos hmiddle_lt grade)
    (source : SixVertexNonNormalizedUnitChargeResidualSources T middle
      hmiddle_pos hmiddle_lt grade)
    (branch : Bool) :
    (family.geometricRepair source branch).target =
      family.surplusTarget (source, branch) :=
  rfl

end SixVertexNonNormalizedPairUnionPhysicalTargetFamily

end

end StatMech.FrontierD
