/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Every sparse candidate short input has its exact genuine preferred label in the U pool. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortPairHalfUPoolCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original supported pair and octad units of each candidate, before actual U acts. -/
noncomputable def monsterNortonPairHalfShortInput (k : Fin 12) :
    NortonPairHalfShortIndex → GriessShortIndex
  | Sum.inl (p, s) => Sum.inl (s, monsterNortonPairHalfPairIndex k p)
  | Sum.inr (d, e) => Sum.inr (Sum.inl
      (monsterNortonOctadIndex (monsterNortonPairHalfOctadCode k d)
        (monsterNortonPairHalfOctad_weight k d), monsterNortonPairHalfOctadSign k d e))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Check all original pair coordinates and genuine pair families through the finite pool lookup.
private theorem pair_lookup (k : Fin 12) (p : Fin 8) (s : Fin 2) :
    let i := monsterNortonPairHalfUPoolStorage k (Sum.inl (p, s))
    monsterNortonPairHalfUPoolInputKind i = 0 ∧
      monsterNortonPairHalfUPoolInputPairFirst i = monsterNortonPairHalfPairFirst k p ∧
      monsterNortonPairHalfUPoolInputPairSecond i = monsterNortonPairHalfPairSecond k p ∧
      monsterNortonPairHalfUPoolInputPairSign i = s := by
  revert k p s
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 32000000 in
-- Check all original source code and preferred even-sign labels through the finite pool lookup.
private theorem octad_lookup (k : Fin 12) (d : Fin 14) (e : Fin 16) :
    let i := monsterNortonPairHalfUPoolStorage k (Sum.inr (d, e))
    monsterNortonPairHalfUPoolInputKind i = 1 ∧
      monsterNortonPairHalfUPoolOctadCode (monsterNortonPairHalfUPoolInputOctadChoice i) =
        monsterNortonPairHalfOctadCode k d ∧
      monsterNortonPairHalfUPoolInputOctadSign i = monsterNortonPairHalfOctadSign k d e := by
  revert k d e
  decide +kernel

/-- Deduplication preserves the full original preferred label of every candidate short unit. -/
theorem monsterNortonPairHalfUPoolLookup_actual (k : Fin 12) (i : NortonPairHalfShortIndex) :
    monsterNortonPairHalfUPoolInput (monsterNortonPairHalfUPoolStorage k i) =
      monsterNortonPairHalfShortInput k i := by
  rcases i with ⟨p, s⟩ | ⟨d, e⟩
  · rcases pair_lookup k p s with ⟨hk, hp, hq, hs⟩
    simp only [monsterNortonPairHalfUPoolInput, hk, ite_true,
      monsterNortonPairHalfShortInput, monsterNortonPairHalfPairIndex, hp, hq, hs]
  · rcases octad_lookup k d e with ⟨hk, hc, he⟩
    simp only [monsterNortonPairHalfUPoolInput, hk, show (1 : ℕ) ≠ 0 by decide, ite_false,
      monsterNortonPairHalfShortInput, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq,
      monsterNortonOctadIndex_eq_iff]
    exact ⟨hc, he⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
