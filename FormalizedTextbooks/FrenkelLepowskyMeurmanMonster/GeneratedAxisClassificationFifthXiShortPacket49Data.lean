/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthXiShortCache

/-! A bounded packet of actual physical Xi preferred-short transport. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 10000 in
/-- Actual target rows of the current support packet. -/
def generatedFifthXiShortPacket49Target (e : Fin 64) : generatedFifthXiShortCachedLabel :=
  Sum.inr (49, e)

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket49Source : Fin 64 → generatedFifthXiShortCachedLabel :=
  ![Sum.inr (24, 0), Sum.inr (48, 61),
    Sum.inr (48, 62), Sum.inr (24, 3),
    Sum.inr (54, 55), Sum.inr (30, 10),
    Sum.inr (30, 9), Sum.inr (54, 52),
    Sum.inr (54, 59), Sum.inr (30, 6),
    Sum.inr (30, 5), Sum.inr (54, 56),
    Sum.inr (24, 12), Sum.inr (48, 49),
    Sum.inr (48, 50), Sum.inr (24, 15),
    Sum.inr (55, 31), Sum.inr (31, 34),
    Sum.inr (31, 33), Sum.inr (55, 28),
    Sum.inr (25, 40), Sum.inr (49, 21),
    Sum.inr (49, 22), Sum.inr (25, 43),
    Sum.inr (25, 36), Sum.inr (49, 25),
    Sum.inr (49, 26), Sum.inr (25, 39),
    Sum.inr (55, 19), Sum.inr (31, 46),
    Sum.inr (31, 45), Sum.inr (55, 16),
    Sum.inr (55, 47), Sum.inr (31, 18),
    Sum.inr (31, 17), Sum.inr (55, 44),
    Sum.inr (25, 24), Sum.inr (49, 37),
    Sum.inr (49, 38), Sum.inr (25, 27),
    Sum.inr (25, 20), Sum.inr (49, 41),
    Sum.inr (49, 42), Sum.inr (25, 23),
    Sum.inr (55, 35), Sum.inr (31, 30),
    Sum.inr (31, 29), Sum.inr (55, 32),
    Sum.inr (24, 48), Sum.inr (48, 13),
    Sum.inr (48, 14), Sum.inr (24, 51),
    Sum.inr (54, 7), Sum.inr (30, 58),
    Sum.inr (30, 57), Sum.inr (54, 4),
    Sum.inr (54, 11), Sum.inr (30, 54),
    Sum.inr (30, 53), Sum.inr (54, 8),
    Sum.inr (24, 60), Sum.inr (48, 1),
    Sum.inr (48, 2), Sum.inr (24, 63)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket49Sign : Fin 64 → ℤ :=
  ![-1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1,
    -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1, -1, 1, 1, -1, 1, -1, -1, 1,
    -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket49Phase : Fin 64 → ZMod 2 :=
  ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1,
    0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 0,
    1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0,
    1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1,
    0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0,
    1, 0, 0, 0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Check 64 genuine source/target vectors in all 24 physical coordinates.
/-- Every displayed physical source has the asserted exact integer Xi image. -/
theorem generatedFifthXiShortPacket49_physical : ∀ e : Fin 64, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket49Source e)) i =
      2 * generatedFifthXiShortPacket49Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket49Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
