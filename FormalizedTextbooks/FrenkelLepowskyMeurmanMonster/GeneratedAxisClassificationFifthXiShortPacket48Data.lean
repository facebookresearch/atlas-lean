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
def generatedFifthXiShortPacket48Target (e : Fin 64) : generatedFifthXiShortCachedLabel :=
  Sum.inr (48, e)

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket48Source : Fin 64 → generatedFifthXiShortCachedLabel :=
  ![Sum.inr (24, 40), Sum.inr (48, 21),
    Sum.inr (48, 22), Sum.inr (24, 43),
    Sum.inr (54, 31), Sum.inr (30, 34),
    Sum.inr (30, 33), Sum.inr (54, 28),
    Sum.inr (54, 19), Sum.inr (30, 46),
    Sum.inr (30, 45), Sum.inr (54, 16),
    Sum.inr (24, 36), Sum.inr (48, 25),
    Sum.inr (48, 26), Sum.inr (24, 39),
    Sum.inr (55, 55), Sum.inr (31, 10),
    Sum.inr (31, 9), Sum.inr (55, 52),
    Sum.inr (25, 0), Sum.inr (49, 61),
    Sum.inr (49, 62), Sum.inr (25, 3),
    Sum.inr (25, 12), Sum.inr (49, 49),
    Sum.inr (49, 50), Sum.inr (25, 15),
    Sum.inr (55, 59), Sum.inr (31, 6),
    Sum.inr (31, 5), Sum.inr (55, 56),
    Sum.inr (55, 7), Sum.inr (31, 58),
    Sum.inr (31, 57), Sum.inr (55, 4),
    Sum.inr (25, 48), Sum.inr (49, 13),
    Sum.inr (49, 14), Sum.inr (25, 51),
    Sum.inr (25, 60), Sum.inr (49, 1),
    Sum.inr (49, 2), Sum.inr (25, 63),
    Sum.inr (55, 11), Sum.inr (31, 54),
    Sum.inr (31, 53), Sum.inr (55, 8),
    Sum.inr (24, 24), Sum.inr (48, 37),
    Sum.inr (48, 38), Sum.inr (24, 27),
    Sum.inr (54, 47), Sum.inr (30, 18),
    Sum.inr (30, 17), Sum.inr (54, 44),
    Sum.inr (54, 35), Sum.inr (30, 30),
    Sum.inr (30, 29), Sum.inr (54, 32),
    Sum.inr (24, 20), Sum.inr (48, 41),
    Sum.inr (48, 42), Sum.inr (24, 23)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket48Sign : Fin 64 → ℤ :=
  ![-1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1,
    -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1, -1, 1, 1, -1, 1, -1, -1, 1,
    -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket48Phase : Fin 64 → ZMod 2 :=
  ![1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 0,
    0, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0,
    1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1,
    1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0,
    0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1,
    1, 0, 0, 0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Check 64 genuine source/target vectors in all 24 physical coordinates.
/-- Every displayed physical source has the asserted exact integer Xi image. -/
theorem generatedFifthXiShortPacket48_physical : ∀ e : Fin 64, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket48Source e)) i =
      2 * generatedFifthXiShortPacket48Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket48Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
