/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual positive triality on the two physical signed-pair short families. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortIdentity
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MatrixPairAction

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Each original signed-pair short unit is its exact physical B,C dictionary combination. -/
theorem monsterNortonPairShort_ABC (s : Fin 2) (p : Fin 276) :
    monsterNortonPureShort (Sum.inl (s, p)) =
      (1 / 2 : ℝ) • trialityABCBasis 2 p +
        (if s = 0 then (1 / 2 : ℝ) else -1 / 2) • trialityABCBasis 1 p := by
  apply trialityBlocksEquiv.injective
  rw [map_add, map_smul, map_smul, trialityABCBasis_blocks, trialityABCBasis_blocks]
  simp only [monsterNortonPureShort, griessConwayDecode, LinearEquiv.apply_symm_apply]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · funext i
    fin_cases s <;> simp
  · funext a q
    fin_cases s <;> fin_cases a <;> by_cases h : q = p <;>
      simp [h]
  · funext d e
    fin_cases s <;> simp
  · funext a k
    fin_cases s <;> fin_cases a <;> simp

/-- Positive extra maps each entire signed-pair short unit to its exact A,C combination. -/
theorem monsterNortonPairShort_extra (s : Fin 2) (p : Fin 276) :
    sExtra (monsterNortonPureShort (Sum.inl (s, p))) =
      (1 / 2 : ℝ) • trialityABCBasis 0 p +
        (if s = 0 then (1 / 2 : ℝ) else -1 / 2) • trialityABCBasis 2 p := by
  rw [monsterNortonPairShort_ABC, map_add, map_smul, map_smul,
    sExtra_ABC_basis, sExtra_ABC_basis]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
