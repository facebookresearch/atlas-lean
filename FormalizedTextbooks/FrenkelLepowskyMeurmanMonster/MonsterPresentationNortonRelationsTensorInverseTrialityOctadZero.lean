/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual inverse triality preserves vanishing of every original octad block. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsTensorInverseTrialityFullCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- An identically zero source octad block remains zero under actual inverse triality. -/
theorem monsterNortonTensor_extra_inverse_octad_zero (x : GriessSpace)
    (hz : ∀ d e, (griessConwayEncode x).2.1 (Sum.inr (Sum.inl (d, e))) = 0)
    (d : Fin 759) (e : Fin 64) :
    (griessConwayEncode (sExtra.symm x)).2.1 (Sum.inr (Sum.inl (d, e))) = 0 := by
  have h : trialityOctadAction (fun r =>
      (griessConwayEncode (sExtra.symm x)).2.1 (Sum.inr (Sum.inl (d, r)))) = 0 := by
    funext r
    have hr := monsterNortonTensor_extra_octad_coordinates (sExtra.symm x) d r
    rw [LinearEquiv.apply_symm_apply] at hr
    exact hr.symm.trans (hz d r)
  have he : (fun r => (griessConwayEncode (sExtra.symm x)).2.1
      (Sum.inr (Sum.inl (d, r)))) = 0 := by
    apply trialityOctadAction.injective
    rw [h, map_zero]
  exact congrFun he e

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
