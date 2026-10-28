/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete forward triality on the original pair and octad preferred units. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsPairTriality
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOctadTriality
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortThird

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Actual forward extra sends one whole preferred octad unit to its 64 exact Fourier rows. -/
theorem monsterNortonOctadPureShort_extra (d : Fin 759) (e : Fin 64) :
    sExtra (monsterNortonPureShort (Sum.inr (Sum.inl (d, e)))) =
      ∑ f : Fin 64, monsterNortonOctadTrialityCoefficient f e •
        monsterNortonPureShort (Sum.inr (Sum.inl (d, f))) := by
  have hi : monsterNortonPureShort (Sum.inr (Sum.inl (d, e))) =
      monsterNortonOctadShortVector d (Pi.single e 1) :=
    (monsterNortonOctadShortVector_single d e 1).symm
  rw [hi, monsterNortonOctadShortVector_extra, monsterNortonOctadShortVector_expansion]
  apply Finset.sum_congr rfl
  intro f _
  rw [monsterNortonOctadTriality_single, mul_one]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
