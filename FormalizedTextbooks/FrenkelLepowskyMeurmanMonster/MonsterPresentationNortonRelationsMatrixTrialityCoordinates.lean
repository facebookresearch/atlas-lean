/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Whole actual positive triality image of a physical pure matrix vector. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsPairTrialityInverse

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Positive triality takes an off-diagonal matrix entry to opposite original pair-short signs. -/
noncomputable def monsterNortonMatrixTrialityShort (A : Matrix (Fin 24) (Fin 24) ℝ) :
    GriessShortIndex → ℝ
  | Sum.inl (s, p) => if s = 0 then A (griessCoordinatePair p).1 (griessCoordinatePair p).2
      else -A (griessCoordinatePair p).1 (griessCoordinatePair p).2
  | _ => 0

/-- The actual diagonal is fixed and every off-diagonal matrix entry becomes its pair-short row. -/
theorem monsterNortonMatrix_extra_actual (A : Matrix (Fin 24) (Fin 24) ℝ) :
    sExtra (griessConwayDecode (A, (0, 0))) =
      griessConwayDecode
        (Matrix.diagonal (fun i => A i i), (monsterNortonMatrixTrialityShort A, 0)) := by
  apply trialityBlocksEquiv.injective
  simp only [sExtra, griessTriality, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  simp only [griessConwayDecode, LinearEquiv.apply_symm_apply, trialityBlockAction,
    LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · funext i
    simp
  · funext s p
    have hc0 : trialityCycle.symm 0 = 2 := by decide
    have hc1 : trialityCycle.symm 1 = 0 := by decide
    have hc2 : trialityCycle.symm 2 = 1 := by decide
    fin_cases s <;>
      simp [trialityCycleAction, hc0, hc1, hc2,
        griessCoordinatePair_ne, monsterNortonMatrixTrialityShort]
  · funext d e
    change trialityOctadAction (0 : Fin 64 → ℝ) e = 0
    exact congrFun (map_zero trialityOctadAction) e
  · funext s k
    simp [trialityCycleAction, monsterNortonMatrixTrialityShort]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
