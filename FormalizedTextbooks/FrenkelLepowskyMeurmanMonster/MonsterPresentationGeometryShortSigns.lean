/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual short-block signs from the original pair, signed-octad, and odd coordinate formulas. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationGeometryShortBase

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The physical first-two-coordinate character of a source Golay label. -/
def monsterGeometryShortCodeSign (d : ℕ) : ℝ :=
  if (golayEncodedMask d).testBit 0 = (golayEncodedMask d).testBit 1 then 1 else -1

/-- Pair coordinates all have positive short-block sign under the chosen actual Q element. -/
theorem monsterGeometryShortBase_pair_sign (s : Fin 2) (p : Fin 276) :
    qSign (qBeta (toAdd monsterGeometryShortBaseQ.base)
          (toAdd (griessShortQ (Sum.inl (s, p))).base) +
        qBeta (toAdd (griessShortQ (Sum.inl (s, p))).base)
          (toAdd monsterGeometryShortBaseQ.base)) = 1 := by
  rw [monsterGeometryShortBase_phase]
  simp only [griessShortIntegral]
  split_ifs <;> norm_num [qSign] <;> decide

/-- Signed-octad signs depend only on whether the octad separates the first two positions. -/
theorem monsterGeometryShortBase_octad_sign (d : Fin 759) (e : Fin 64) :
    qSign (qBeta (toAdd monsterGeometryShortBaseQ.base)
          (toAdd (griessShortQ (Sum.inr (Sum.inl (d, e)))).base) +
        qBeta (toAdd (griessShortQ (Sum.inr (Sum.inl (d, e)))).base)
          (toAdd monsterGeometryShortBaseQ.base)) =
      monsterGeometryShortCodeSign (golayOctadLabel d).val := by
  rw [monsterGeometryShortBase_phase]
  change qSign (((((if (golayEncodedMask (golayOctadLabel d).val).testBit 0 then
    if (griessOctadSignMask d e).testBit 0 then -2 else 2 else 0) -
    (if (golayEncodedMask (golayOctadLabel d).val).testBit 1 then
    if (griessOctadSignMask d e).testBit 1 then -2 else 2 else 0)) / 2 : ℤ) : ZMod 2)) = _
  cases h0 : (golayEncodedMask (golayOctadLabel d).val).testBit 0 <;>
    cases h1 : (golayEncodedMask (golayOctadLabel d).val).testBit 1 <;>
    cases hs0 : (griessOctadSignMask d e).testBit 0 <;>
    cases hs1 : (griessOctadSignMask d e).testBit 1 <;>
    simp_all only [monsterGeometryShortCodeSign,
      Bool.false_eq_true, Bool.true_eq_false, eq_self, ite_true, ite_false] <;>
    norm_num [qSign] <;> decide

/-- Odd-coordinate signs depend only on the same source code character, not the special position. -/
theorem monsterGeometryShortBase_odd_sign (d : Fin 2048) (j : Fin 24) :
    qSign (qBeta (toAdd monsterGeometryShortBaseQ.base)
          (toAdd (griessShortQ (Sum.inr (Sum.inr (d, j)))).base) +
        qBeta (toAdd (griessShortQ (Sum.inr (Sum.inr (d, j)))).base)
          (toAdd monsterGeometryShortBaseQ.base)) =
      monsterGeometryShortCodeSign d.val := by
  rw [monsterGeometryShortBase_phase]
  change qSign (((((if (golayEncodedMask d.val).testBit 0 then -1 else 1) *
    (if (0 : Fin 24) = j then -3 else 1) -
    (if (golayEncodedMask d.val).testBit 1 then -1 else 1) *
    (if (1 : Fin 24) = j then -3 else 1)) / 2 : ℤ) : ZMod 2)) = _
  by_cases h0j : (0 : Fin 24) = j <;> by_cases h1j : (1 : Fin 24) = j <;>
    cases h0 : (golayEncodedMask d.val).testBit 0 <;>
    cases h1 : (golayEncodedMask d.val).testBit 1 <;>
    simp only [monsterGeometryShortCodeSign, h0, h1, h0j, h1j,
      Bool.false_eq_true, Bool.true_eq_false, eq_self, ite_true, ite_false] <;>
    norm_num [qSign] <;> decide

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
