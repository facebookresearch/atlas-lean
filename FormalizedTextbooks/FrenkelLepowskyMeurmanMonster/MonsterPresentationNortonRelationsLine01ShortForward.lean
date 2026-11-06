/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact forward Norton action on all reached inverse short images. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01ShortInverse

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem subgroup_inv_apply (S : Subgroup (GriessSpace ≃ₗ[ℝ] GriessSpace))
    (g : S) (x : GriessSpace) : g.val ((g⁻¹).val x) = x :=
  LinearEquiv.apply_symm_apply g.val x

/-- Actual Norton u returns every signed inverse short image to its original source X vector. -/
theorem monsterNortonLine01ShortForward_signed (a : Fin 64) (k : Fin 16) :
    y555NortonActualU.val (griessConwayDecode (0,
      (qSign (monsterNortonLine01ShortInversePhase a k) •
        Pi.single (monsterNortonLine01ShortInverseOutput a k) 1, 0))) =
      trialityXYZBasis 0 (finProdFinEquiv
        (monsterNortonLine01ShortInputCode a, monsterNortonLine01ShortPhysicalColumn k)) := by
  have h := congrArg (fun x : GriessSpace => y555NortonActualU.val x)
    (monsterNortonLine01ShortInverse_actual a k)
  rw [subgroup_inv_apply] at h
  exact h.symm

private theorem decode_scaled_short (c : ℝ) (X : GriessShortIndex → ℝ) :
    griessConwayDecode (0, (c • X, 0)) = c • griessConwayDecode (0, (X, 0)) := by
  have h : ((0, (c • X, 0)) : ConwayRawSpace) = c • (0, (X, 0)) := by
    simp only [Prod.smul_mk, smul_zero]
  change griessConwayDecodeLinear (0, (c • X, 0)) =
    c • griessConwayDecodeLinear (0, (X, 0))
  rw [h, map_smul]

/-- The forward image of every reached short unit has its original actual inverse phase. -/
theorem monsterNortonLine01ShortForward_actual (a : Fin 64) (k : Fin 16) :
    y555NortonActualU.val (griessConwayDecode (0,
      (Pi.single (monsterNortonLine01ShortInverseOutput a k) 1, 0))) =
      qSign (monsterNortonLine01ShortInversePhase a k) •
        trialityXYZBasis 0 (finProdFinEquiv
          (monsterNortonLine01ShortInputCode a, monsterNortonLine01ShortPhysicalColumn k)) := by
  have h := monsterNortonLine01ShortForward_signed a k
  rw [decode_scaled_short, map_smul] at h
  have hh := congrArg (fun x : GriessSpace =>
    qSign (monsterNortonLine01ShortInversePhase a k) • x) h
  simpa only [smul_smul, qSign_sq, one_smul] using hh

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
