/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Full source triality on every original pure physical matrix. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsPairMatrixUTwo

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The complete B short coordinates obtained from the off-diagonal physical matrix entries. -/
def monsterNortonDistanceTwoMatrixTrialityShort (A : Matrix (Fin 24) (Fin 24) ℝ) :
    GriessShortIndex → ℝ
  | Sum.inl (s, p) =>
      if s = 0 then A (griessCoordinatePair p).1 (griessCoordinatePair p).2
      else -A (griessCoordinatePair p).1 (griessCoordinatePair p).2
  | Sum.inr _ => 0

/-- Every whole pure matrix has the exact fixed diagonal and cycled B coordinates under extra. -/
theorem monsterNortonMatrix_extra (A : Matrix (Fin 24) (Fin 24) ℝ) :
    sExtra (griessConwayDecode (A, (0, 0))) =
      griessConwayDecode (Matrix.diagonal (fun i => A i i),
        (monsterNortonDistanceTwoMatrixTrialityShort A, 0)) := by
  apply trialityBlocksEquiv.injective
  change trialityBlocksEquiv (griessTriality (griessConwayDecode (A, (0, 0)))) = _
  rw [griessTriality, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  simp only [griessConwayDecode, LinearEquiv.apply_symm_apply, trialityBlockAction,
    LinearEquiv.prodCongr_apply]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · funext i
    simp only [LinearEquiv.refl_apply, Matrix.diagonal_apply_eq]
  · funext s p
    have h0 : trialityCycle.symm 0 = 2 := by decide +kernel
    have h1 : trialityCycle.symm 1 = 0 := by decide +kernel
    have h2 : trialityCycle.symm 2 = 1 := by decide +kernel
    fin_cases s <;> simp [trialityCycleAction, h0, h1, h2,
      monsterNortonDistanceTwoMatrixTrialityShort, griessCoordinatePair_ne]
  · funext d e
    change trialityOctadAction (0 : Fin 64 → ℝ) e = 0
    rw [map_zero]
    rfl
  · funext s k
    fin_cases s <;> simp [trialityCycleAction, monsterNortonDistanceTwoMatrixTrialityShort]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
