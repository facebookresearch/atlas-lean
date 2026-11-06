/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthSupportEnumeration
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityOrder
@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The actual final triality takes each octad block through the source's exact DH matrix. -/
theorem generatedFourthQShortBasis_triality_octad (x : GriessSpace) (o : Fin 759) (e : Fin 64) :
    (griessConwayEncode (sExtra x)).2.1 (Sum.inr (Sum.inl (o, e))) =
      ∑ f : Fin 64, trialityRealMatrix e f *
        (griessConwayEncode x).2.1 (Sum.inr (Sum.inl (o, f))) := by
  have h : (griessConwayEncode (sExtra x)).2.1 (Sum.inr (Sum.inl (o, e))) =
      trialityOctadAction (fun f => (griessConwayEncode x).2.1
        (Sum.inr (Sum.inl (o, f)))) e := by
    simp [griessConwayEncode, sExtra, griessTriality, trialityBlockAction]
  rw [h, trialityOctadAction_matrix]
  rfl

/-- The actual final minus-pair coordinate retains both its old matrix and old short terms. -/
theorem generatedFourthQShortBasis_triality_pair_minus (x : GriessSpace) (p : Fin 276) :
    (griessConwayEncode (sExtra x)).2.1 (Sum.inl (0, p)) =
      (griessConwayEncode x).1 (griessCoordinatePair p).1 (griessCoordinatePair p).2 +
      ((griessConwayEncode x).2.1 (Sum.inl (0, p)) -
        (griessConwayEncode x).2.1 (Sum.inl (1, p))) / 2 := by
  have hn := griessCoordinatePair_ne p
  have h0 : trialityCycle.symm 1 = 0 := by decide
  have h1 : trialityCycle.symm 2 = 1 := by decide
  simp [griessConwayEncode, sExtra, griessTriality, trialityBlockAction,
    trialityCycleAction, h0, h1, hn, griessPairIndex_pair]
  ring

/-- The actual final plus-pair coordinate retains both its old matrix and old short terms. -/
theorem generatedFourthQShortBasis_triality_pair_plus (x : GriessSpace) (p : Fin 276) :
    (griessConwayEncode (sExtra x)).2.1 (Sum.inl (1, p)) =
      ((griessConwayEncode x).2.1 (Sum.inl (0, p)) -
        (griessConwayEncode x).2.1 (Sum.inl (1, p))) / 2 -
      (griessConwayEncode x).1 (griessCoordinatePair p).1 (griessCoordinatePair p).2 := by
  have hn := griessCoordinatePair_ne p
  have h0 : trialityCycle.symm 1 = 0 := by decide
  have h1 : trialityCycle.symm 2 = 1 := by decide
  simp [griessConwayEncode, sExtra, griessTriality, trialityBlockAction,
    trialityCycleAction, h0, h1, hn, griessPairIndex_pair]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
