/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact finite pairings bind twelve whole actual forward half-word images to sparse packets. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortPairHalfCoefficientData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Integer numerator of each finite source candidate coefficient. -/
def monsterNortonPairHalfNumerator (k : Fin 12) : NortonPairHalfIndex → ℤ
  | Sum.inl i => monsterNortonPairHalfPairCoefficient k i
  | Sum.inr (Sum.inl i) => monsterNortonPairHalfPairCCoefficient k i
  | Sum.inr (Sum.inr (d, e)) => monsterNortonPairHalfOctadCoefficient k d e

/-- Exact integer source norm weights are two for A and C and one for octad units. -/
def monsterNortonPairHalfIntegerWeight : NortonPairHalfIndex → ℤ
  | Sum.inl _ => 2
  | Sum.inr (Sum.inl _) => 2
  | Sum.inr (Sum.inr _) => 1

set_option maxRecDepth 10000 in
set_option maxHeartbeats 128000000 in
-- Verify all 2880 support pairings against all sixty-four actual phase-complete terms.
/-- Every actual support pairing has precisely the finite candidate numerator and norm weight. -/
theorem monsterNortonPairHalfPairings_integer (k : Fin 12) (i : NortonPairHalfIndex) :
    monsterNortonPairHalfInitialSign k *
      (∑ e : Fin 64, monsterNortonPairHalfSixthInteger k e * monsterNortonPairHalfGram k e i) =
      4 * monsterNortonPairHalfNumerator k i * monsterNortonPairHalfIntegerWeight i := by
  revert k i
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
