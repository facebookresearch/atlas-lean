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
def generatedFifthXiShortPacket14Target (e : Fin 64) : generatedFifthXiShortCachedLabel :=
  Sum.inr (14, e)

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket14Source : Fin 64 → generatedFifthXiShortCachedLabel :=
  ![Sum.inr (21, 55), Sum.inr (16, 10),
    Sum.inr (16, 9), Sum.inr (21, 52),
    Sum.inr (15, 0), Sum.inr (18, 61),
    Sum.inr (18, 62), Sum.inr (15, 3),
    Sum.inr (15, 12), Sum.inr (18, 49),
    Sum.inr (18, 50), Sum.inr (15, 15),
    Sum.inr (21, 59), Sum.inr (16, 6),
    Sum.inr (16, 5), Sum.inr (21, 56),
    Sum.inr (19, 40), Sum.inr (14, 21),
    Sum.inr (14, 22), Sum.inr (19, 43),
    Sum.inr (17, 31), Sum.inr (20, 34),
    Sum.inr (20, 33), Sum.inr (17, 28),
    Sum.inr (17, 19), Sum.inr (20, 46),
    Sum.inr (20, 45), Sum.inr (17, 16),
    Sum.inr (19, 36), Sum.inr (14, 25),
    Sum.inr (14, 26), Sum.inr (19, 39),
    Sum.inr (19, 24), Sum.inr (14, 37),
    Sum.inr (14, 38), Sum.inr (19, 27),
    Sum.inr (17, 47), Sum.inr (20, 18),
    Sum.inr (20, 17), Sum.inr (17, 44),
    Sum.inr (17, 35), Sum.inr (20, 30),
    Sum.inr (20, 29), Sum.inr (17, 32),
    Sum.inr (19, 20), Sum.inr (14, 41),
    Sum.inr (14, 42), Sum.inr (19, 23),
    Sum.inr (21, 7), Sum.inr (16, 58),
    Sum.inr (16, 57), Sum.inr (21, 4),
    Sum.inr (15, 48), Sum.inr (18, 13),
    Sum.inr (18, 14), Sum.inr (15, 51),
    Sum.inr (15, 60), Sum.inr (18, 1),
    Sum.inr (18, 2), Sum.inr (15, 63),
    Sum.inr (21, 11), Sum.inr (16, 54),
    Sum.inr (16, 53), Sum.inr (21, 8)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket14Sign : Fin 64 → ℤ :=
  ![1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1,
    1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1, 1, -1, -1, 1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket14Phase : Fin 64 → ZMod 2 :=
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
theorem generatedFifthXiShortPacket14_physical : ∀ e : Fin 64, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket14Source e)) i =
      2 * generatedFifthXiShortPacket14Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket14Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
