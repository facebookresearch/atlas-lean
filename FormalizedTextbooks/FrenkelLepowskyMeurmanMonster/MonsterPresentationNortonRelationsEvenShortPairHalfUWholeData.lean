/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Full matrix and short packets for the twelve actual sparse-candidate U transports. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortPairHalfUPoolLookup
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsPairMatrixU

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The genuine preferred output label of each short unit under actual U. -/
noncomputable def monsterNortonPairHalfShortUOutput (k : Fin 12)
    (i : NortonPairHalfShortIndex) : GriessShortIndex :=
  monsterNortonPairHalfUPoolOutput (monsterNortonPairHalfUPoolStorage k i)

/-- Actual short input scalars preserve each candidate's original denominator sixteen. -/
noncomputable def monsterNortonPairHalfShortCoefficient (k : Fin 12) :
    NortonPairHalfShortIndex → ℝ
  | Sum.inl (p, _) => (monsterNortonPairHalfPairCCoefficient k p : ℝ) / 16
  | Sum.inr (d, e) => (monsterNortonPairHalfOctadCoefficient k d e : ℝ) / 16

/-- The complete pure-matrix part consists of eight actual transported source A units. -/
noncomputable def monsterNortonPairHalfUMatrixPacket (k : Fin 12) : GriessSpace :=
  ∑ p : Fin 8, ((monsterNortonPairHalfPairCoefficient k p : ℝ) / 16) •
    griessConwayDecode (conwayMatrixAction monsterNortonUFiber.val.2
      (trialityPairMatrix (monsterNortonPairHalfPairIndex k p)), (0, 0))

/-- The complete short part contains all 240 true phase-checked preferred U images. -/
noncomputable def monsterNortonPairHalfUShortPacket (k : Fin 12) : GriessSpace :=
  ∑ i : NortonPairHalfShortIndex, monsterNortonPairHalfShortCoefficient k i •
    monsterNortonPureShort (monsterNortonPairHalfShortUOutput k i)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
