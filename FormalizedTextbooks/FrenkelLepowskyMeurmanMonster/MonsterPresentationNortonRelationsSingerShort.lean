/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual zero-phase Singer lift permutes preferred short units without extra signs. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsSingerTensor
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortQCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The actual preferred-Q coefficient remains zero under the genuine Singer permutation. -/
theorem monsterNortonSinger_short_phase (r : GriessShortIndex) :
    localShortPhase monsterNortonSingerFiber r = 0 := by
  change toAdd (spinConjugation monsterNortonSingerSpin (griessShortQ r)).coeff = 0
  rw [monsterNortonSingerSpin_conjugation]
  rfl

private theorem short_q_injective : Function.Injective griessShortQ := by
  intro r s h
  apply griessShortClass_injective
  apply leechHyperbolicCoordinates.injective
  have hb := congrArg (fun q : Q => toAdd q.base) h
  have hbase (t : GriessShortIndex) : toAdd (griessShortQ t).base =
      leechHyperbolicCoordinates (griessShortClass t) := rfl
  rw [hbase, hbase] at hb
  exact hb

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Check the full actual Q source labels of all twenty-four zero-code odd short vectors.
/-- The zero-code odd short labels have exactly the physical coordinate permutation action. -/
theorem monsterNortonSinger_odd_zero_source_certificate (i : Fin 24) :
    monsterNortonSingerImage
      (monsterNortonShortQSource (Sum.inr (Sum.inr (0, i)))) =
      monsterNortonShortQSource
        (Sum.inr (Sum.inr (0, monsterNortonSingerPermutation 0 i))) := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    change (fun j : Fin 24 => toAdd
      (monsterNortonSingerImage
        (monsterNortonShortQSource (Sum.inr (Sum.inr (0, i))))).base j) =
      (fun j : Fin 24 => toAdd (monsterNortonShortQSource
        (Sum.inr (Sum.inr (0, monsterNortonSingerPermutation 0 i)))).base j)
    fin_cases i <;> decide +kernel
  · rfl

/-- The intrinsic actual short permutation agrees with the physical zero-code odd permutation. -/
theorem monsterNortonSinger_odd_zero_permutation (i : Fin 24) :
    griessShortPermutation (monsterNortonSingerPermutationIsometry 0)
      (Sum.inr (Sum.inr (0, i))) =
        Sum.inr (Sum.inr (0, monsterNortonSingerPermutation 0 i)) := by
  apply short_q_injective
  have h := griessShortQ_image monsterNortonSingerFiber (Sum.inr (Sum.inr (0, i)))
  rw [monsterNortonSinger_short_phase, (show qCentral (0 : ZMod 2) = 1 from rfl), one_mul] at h
  change spinConjugation monsterNortonSingerSpin
      (griessShortQ (Sum.inr (Sum.inr (0, i)))) = _ at h
  rw [monsterNortonSingerSpin_conjugation,
    ← monsterNortonShortQSource_actual (Sum.inr (Sum.inr (0, i))),
    monsterNortonSinger_odd_zero_source_certificate,
    monsterNortonShortQSource_actual] at h
  exact h.symm

/-- Every actual preferred short unit is carried to its unsigned Singer permutation image. -/
theorem monsterNortonSinger_short_unit (r : GriessShortIndex) :
    localShortRepresentation monsterNortonSingerFiber (Pi.single r 1) =
      Pi.single (griessShortPermutation (monsterNortonSingerPermutationIsometry 0) r) 1 := by
  ext s
  obtain ⟨k, rfl⟩ :=
    (griessShortPermutation (monsterNortonSingerPermutationIsometry 0)).surjective s
  change localShortOperator monsterNortonSingerFiber (Pi.single r 1)
    (griessShortPermutation (monsterNortonSingerPermutationIsometry 0) k) = _
  have h := localShortOperator_image monsterNortonSingerFiber (Pi.single r 1) k
  change localShortOperator monsterNortonSingerFiber (Pi.single r 1)
    (griessShortPermutation (monsterNortonSingerPermutationIsometry 0) k) = _ at h
  rw [monsterNortonSinger_short_phase, qSign_zero, one_mul] at h
  rw [h]
  simp [Pi.single_apply]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
