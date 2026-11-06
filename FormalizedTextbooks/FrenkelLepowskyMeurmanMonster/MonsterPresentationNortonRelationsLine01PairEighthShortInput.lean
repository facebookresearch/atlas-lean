/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual pair/octet input labels for the eighth operator of the first Norton line-square test. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairEighthShortData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The first coordinate of each of the sixteen displayed adjacent-pair short units. -/
def monsterNortonLine01PairEighthInputPairFirst (k : Fin 16) : Fin 24 :=
  ⟨2 * (k.val % 8), by have hm := Nat.mod_lt k.val (by decide : 0 < 8); omega⟩

/-- The second coordinate of that original increasing pair. -/
def monsterNortonLine01PairEighthInputPairSecond (k : Fin 16) : Fin 24 :=
  ⟨2 * (k.val % 8) + 1, by have hm := Nat.mod_lt k.val (by decide : 0 < 8); omega⟩

/-- These are all genuine increasing physical pairs. -/
theorem monsterNortonLine01PairEighthInputPair_increasing (k : Fin 16) :
    monsterNortonLine01PairEighthInputPairFirst k <
      monsterNortonLine01PairEighthInputPairSecond k := by
  change 2 * (k.val % 8) < 2 * (k.val % 8) + 1
  omega

/-- The fourteen actual source octad slots after the first sixteen pair inputs. -/
def monsterNortonLine01PairEighthInputOctadSlot (k : Fin 240) (hk : ¬k.val < 16) : Fin 14 :=
  ⟨(k.val - 16) / 16, by omega⟩

/-- The sixteen checked original even-sign slots in each octad support. -/
def monsterNortonLine01PairEighthInputSignSlot (k : Fin 240) : Fin 16 :=
  ⟨(k.val - 16) % 16, Nat.mod_lt _ (by decide)⟩

/-- All 240 original shortest-vector labels on which the eighth-step U must be checked. -/
noncomputable def monsterNortonLine01PairEighthShortInput (k : Fin 240) : GriessShortIndex :=
  if hk : k.val < 16 then
    let j : Fin 16 := ⟨k.val, hk⟩
    Sum.inl ((if j.val < 8 then 0 else 1),
      griessPairIndex (monsterNortonLine01PairEighthInputPairFirst j)
        (monsterNortonLine01PairEighthInputPairSecond j)
        (ne_of_lt (monsterNortonLine01PairEighthInputPair_increasing j)))
  else
    let a := monsterNortonLine01PairEighthInputOctadSlot k hk
    Sum.inr (Sum.inl
      (monsterNortonOctadIndex (monsterNortonLine01PairInverseOctadCodes a)
        (monsterNortonLine01PairInverseOctad_weight a),
      monsterNortonLine01PairSeventhOctadSupport a (monsterNortonLine01PairEighthInputSignSlot k)))

/-- The complete finite physical integer vector of every eighth-step input. -/
def monsterNortonLine01PairEighthInputIntegral (k : Fin 240) : Fin 24 → ℤ :=
  if hk : k.val < 16 then
    let j : Fin 16 := ⟨k.val, hk⟩
    fun i => 4 * (if i = monsterNortonLine01PairEighthInputPairFirst j then 1 else 0) +
      (if j.val < 8 then -4 else 4) *
        (if i = monsterNortonLine01PairEighthInputPairSecond j then 1 else 0)
  else
    let a := monsterNortonLine01PairEighthInputOctadSlot k hk
    monsterNortonOctadIntegral (monsterNortonLine01PairInverseOctadCodes a)
      (monsterNortonLine01PairInverseOctadPositions a)
      (monsterNortonLine01PairSeventhOctadSupport a (monsterNortonLine01PairEighthInputSignSlot k))

/-- Every finite input agrees with the actual original Conway shortest-vector dictionary. -/
theorem monsterNortonLine01PairEighthInputIntegral_actual (k : Fin 240) :
    griessShortIntegral (monsterNortonLine01PairEighthShortInput k) =
      monsterNortonLine01PairEighthInputIntegral k := by
  unfold monsterNortonLine01PairEighthShortInput monsterNortonLine01PairEighthInputIntegral
  by_cases hk : k.val < 16
  · simp only [dite_eq_left hk, griessShortIntegral, griessPairIndex_coordinates,
      monsterNortonLine01PairEighthInputPair_increasing, ite_true]
    by_cases hf : k.val < 8 <;> simp [hf]
  · simp only [dite_eq_right hk]
    exact monsterNortonOctadIntegral_eq
      (monsterNortonLine01PairInverseOctadCodes (monsterNortonLine01PairEighthInputOctadSlot k hk))
      (monsterNortonLine01PairInverseOctad_weight
        (monsterNortonLine01PairEighthInputOctadSlot k hk))
      (monsterNortonLine01PairInverseOctadPositions
        (monsterNortonLine01PairEighthInputOctadSlot k hk))
      (monsterNortonLine01PairInverseOctad_coordinate
        (monsterNortonLine01PairEighthInputOctadSlot k hk))
      (monsterNortonLine01PairSeventhOctadSupport (monsterNortonLine01PairEighthInputOctadSlot k hk)
        (monsterNortonLine01PairEighthInputSignSlot k))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
