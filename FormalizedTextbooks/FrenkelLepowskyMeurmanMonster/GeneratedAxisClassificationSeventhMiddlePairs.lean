/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhQConjugation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhPairCoefficients
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhPairZero

/-! The three surviving middle pair rows have their actual preferred-Q signs. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The three genuine transported minus-pair coefficients are exactly one quarter. -/
theorem generatedSeventh_middle_selected_pair (j : Fin 3) :
    (griessConwayEncode
      (rhoLocal (localFiberIntoH generatedSeventhLocalFiber) generatedOddAxis)).2.1
        (Sum.inl (0, generatedSeventhTargetPair j)) =
      (1 / 4 : ℝ) := by
  rw [generatedFourth_local_short, ← generatedSeventh_pair_permutation j,
    localShortOperator_image, generatedSeventh_pair_phase, qSign_zero, one_mul,
    generatedSeventh_source_pair_coefficient]

/-- The complete physical coefficient table for the middle pair block. -/
def generatedSeventhMiddlePairValue (s : Fin 2) (a b : Fin 24) : ℝ :=
  if s = 0 then
    if (a = 16 ∧ b = 17) ∨ (a = 16 ∧ b = 19) ∨ (a = 17 ∧ b = 19) then 1 / 4 else 0
  else 0

private theorem target_pair_eq (p : Fin 276) (j : Fin 3)
    (hp : griessCoordinatePair p = generatedSeventhTargetCoordinates j) :
    p = generatedSeventhTargetPair j := by
  apply griessCoordinatePairEquiv.injective
  apply Subtype.ext
  change griessCoordinatePair p = griessCoordinatePair (generatedSeventhTargetPair j)
  exact hp.trans (generatedSeventh_pair_coordinate_certificate j).2.symm

/-- Every actual middle pair coefficient agrees with the sparse physical table. -/
theorem generatedSeventh_middle_pair_coordinate (s : Fin 2) (p : Fin 276) :
    (griessConwayEncode
      (rhoLocal (localFiberIntoH generatedSeventhLocalFiber) generatedOddAxis)).2.1
        (Sum.inl (s, p)) =
      generatedSeventhMiddlePairValue s (griessCoordinatePair p).1
        (griessCoordinatePair p).2 := by
  by_cases hp : generatedSeventhPairExceptional s
      (griessCoordinatePair p).1 (griessCoordinatePair p).2
  · rcases hp with ⟨hs, hp | hp | hp⟩ <;> subst s
    · have h := target_pair_eq p 0 (Prod.ext hp.1 hp.2)
      subst p
      rw [generatedSeventh_middle_selected_pair,
        (generatedSeventh_pair_coordinate_certificate 0).2]
      norm_num [generatedSeventhMiddlePairValue]
    · have h := target_pair_eq p 1 (Prod.ext hp.1 hp.2)
      subst p
      rw [generatedSeventh_middle_selected_pair,
        (generatedSeventh_pair_coordinate_certificate 1).2]
      norm_num [generatedSeventhMiddlePairValue]
    · have h := target_pair_eq p 2 (Prod.ext hp.1 hp.2)
      subst p
      rw [generatedSeventh_middle_selected_pair,
        (generatedSeventh_pair_coordinate_certificate 2).2]
      norm_num [generatedSeventhMiddlePairValue]
  · rw [generatedSeventh_middle_pair_zero s p hp]
    unfold generatedSeventhPairExceptional at hp
    simp only [generatedSeventhMiddlePairValue]
    split_ifs <;> tauto

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
