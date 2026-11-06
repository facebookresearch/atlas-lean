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
def generatedFifthXiShortPacket31Target (e : Fin 64) : generatedFifthXiShortCachedLabel :=
  Sum.inr (31, e)

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket31Source : Fin 64 → generatedFifthXiShortCachedLabel :=
  ![Sum.inr (24, 55), Sum.inr (48, 10),
    Sum.inr (48, 9), Sum.inr (24, 52),
    Sum.inr (54, 0), Sum.inr (30, 61),
    Sum.inr (30, 62), Sum.inr (54, 3),
    Sum.inr (54, 12), Sum.inr (30, 49),
    Sum.inr (30, 50), Sum.inr (54, 15),
    Sum.inr (24, 59), Sum.inr (48, 6),
    Sum.inr (48, 5), Sum.inr (24, 56),
    Sum.inr (55, 40), Sum.inr (31, 21),
    Sum.inr (31, 22), Sum.inr (55, 43),
    Sum.inr (25, 31), Sum.inr (49, 34),
    Sum.inr (49, 33), Sum.inr (25, 28),
    Sum.inr (25, 19), Sum.inr (49, 46),
    Sum.inr (49, 45), Sum.inr (25, 16),
    Sum.inr (55, 36), Sum.inr (31, 25),
    Sum.inr (31, 26), Sum.inr (55, 39),
    Sum.inr (55, 24), Sum.inr (31, 37),
    Sum.inr (31, 38), Sum.inr (55, 27),
    Sum.inr (25, 47), Sum.inr (49, 18),
    Sum.inr (49, 17), Sum.inr (25, 44),
    Sum.inr (25, 35), Sum.inr (49, 30),
    Sum.inr (49, 29), Sum.inr (25, 32),
    Sum.inr (55, 20), Sum.inr (31, 41),
    Sum.inr (31, 42), Sum.inr (55, 23),
    Sum.inr (24, 7), Sum.inr (48, 58),
    Sum.inr (48, 57), Sum.inr (24, 4),
    Sum.inr (54, 48), Sum.inr (30, 13),
    Sum.inr (30, 14), Sum.inr (54, 51),
    Sum.inr (54, 60), Sum.inr (30, 1),
    Sum.inr (30, 2), Sum.inr (54, 63),
    Sum.inr (24, 11), Sum.inr (48, 54),
    Sum.inr (48, 53), Sum.inr (24, 8)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket31Sign : Fin 64 → ℤ :=
  ![1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1,
    1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1, 1, -1, -1, 1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket31Phase : Fin 64 → ZMod 2 :=
  ![0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0,
    1, 1, 1, 0, 1, 0, 0, 0, 1, 1, 1, 0,
    1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0,
    1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 1,
    1, 1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 1,
    0, 0, 0, 1]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Check 64 genuine source/target vectors in all 24 physical coordinates.
/-- Every displayed physical source has the asserted exact integer Xi image. -/
theorem generatedFifthXiShortPacket31_physical : ∀ e : Fin 64, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket31Source e)) i =
      2 * generatedFifthXiShortPacket31Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket31Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
