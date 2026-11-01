/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthQConjugation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthPairCoefficients
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthPairZero

/-! The three surviving middle pair rows have their actual preferred-Q signs. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The three genuine transported minus-pair coefficients are exactly 1/4, -3/4, -3/4. -/
theorem generatedSixth_middle_selected_pair (j : Fin 3) :
    (griessConwayEncode
      (rhoLocal (localFiberIntoH generatedSixthLocalFiber) generatedOddAxis)).2.1
        (Sum.inl (0, generatedSixthTargetPair j)) =
      if j = 0 then 1 / 4 else -3 / 4 := by
  rw [generatedFourth_local_short, ← generatedSixth_pair_permutation j,
    localShortOperator_image, generatedSixth_pair_phase, qSign_zero, one_mul,
    generatedSixth_source_pair_coefficient]

/-- The complete physical coefficient table for the middle pair block. -/
def generatedSixthMiddlePairValue (s : Fin 2) (a b : Fin 24) : ℝ :=
  if s = 0 then
    if a = 16 ∧ b = 17 then 1 / 4 else
      if (a = 16 ∧ b = 19) ∨ (a = 17 ∧ b = 19) then -3 / 4 else 0
  else 0

private theorem target_pair_eq (p : Fin 276) (j : Fin 3)
    (hp : griessCoordinatePair p = generatedSixthTargetCoordinates j) :
    p = generatedSixthTargetPair j := by
  apply griessCoordinatePairEquiv.injective
  apply Subtype.ext
  change griessCoordinatePair p = griessCoordinatePair (generatedSixthTargetPair j)
  exact hp.trans (generatedSixth_pair_coordinate_certificate j).2.symm

/-- Every actual middle pair coefficient agrees with the sparse physical table. -/
theorem generatedSixth_middle_pair_coordinate (s : Fin 2) (p : Fin 276) :
    (griessConwayEncode
      (rhoLocal (localFiberIntoH generatedSixthLocalFiber) generatedOddAxis)).2.1
        (Sum.inl (s, p)) =
      generatedSixthMiddlePairValue s (griessCoordinatePair p).1
        (griessCoordinatePair p).2 := by
  by_cases hp : generatedSixthPairExceptional s
      (griessCoordinatePair p).1 (griessCoordinatePair p).2
  · rcases hp with ⟨hs, hp | hp | hp⟩ <;> subst s
    · have h := target_pair_eq p 0 (Prod.ext hp.1 hp.2)
      subst p
      rw [generatedSixth_middle_selected_pair,
        (generatedSixth_pair_coordinate_certificate 0).2]
      norm_num [generatedSixthMiddlePairValue]
    · have h := target_pair_eq p 1 (Prod.ext hp.1 hp.2)
      subst p
      rw [generatedSixth_middle_selected_pair,
        (generatedSixth_pair_coordinate_certificate 1).2]
      norm_num [generatedSixthMiddlePairValue]
    · have h := target_pair_eq p 2 (Prod.ext hp.1 hp.2)
      subst p
      rw [generatedSixth_middle_selected_pair,
        (generatedSixth_pair_coordinate_certificate 2).2]
      norm_num [generatedSixthMiddlePairValue]
  · rw [generatedSixth_middle_pair_zero s p hp]
    unfold generatedSixthPairExceptional at hp
    simp only [generatedSixthMiddlePairValue]
    split_ifs <;> tauto

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
