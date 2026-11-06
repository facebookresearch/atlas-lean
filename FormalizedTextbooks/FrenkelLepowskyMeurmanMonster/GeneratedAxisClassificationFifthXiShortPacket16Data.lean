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
def generatedFifthXiShortPacket16Target (e : Fin 64) : generatedFifthXiShortCachedLabel :=
  Sum.inr (16, e)

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket16Source : Fin 64 → generatedFifthXiShortCachedLabel :=
  ![Sum.inr (21, 40), Sum.inr (16, 21),
    Sum.inr (16, 22), Sum.inr (21, 43),
    Sum.inr (15, 31), Sum.inr (18, 34),
    Sum.inr (18, 33), Sum.inr (15, 28),
    Sum.inr (15, 19), Sum.inr (18, 46),
    Sum.inr (18, 45), Sum.inr (15, 16),
    Sum.inr (21, 36), Sum.inr (16, 25),
    Sum.inr (16, 26), Sum.inr (21, 39),
    Sum.inr (19, 55), Sum.inr (14, 10),
    Sum.inr (14, 9), Sum.inr (19, 52),
    Sum.inr (17, 0), Sum.inr (20, 61),
    Sum.inr (20, 62), Sum.inr (17, 3),
    Sum.inr (17, 12), Sum.inr (20, 49),
    Sum.inr (20, 50), Sum.inr (17, 15),
    Sum.inr (19, 59), Sum.inr (14, 6),
    Sum.inr (14, 5), Sum.inr (19, 56),
    Sum.inr (19, 7), Sum.inr (14, 58),
    Sum.inr (14, 57), Sum.inr (19, 4),
    Sum.inr (17, 48), Sum.inr (20, 13),
    Sum.inr (20, 14), Sum.inr (17, 51),
    Sum.inr (17, 60), Sum.inr (20, 1),
    Sum.inr (20, 2), Sum.inr (17, 63),
    Sum.inr (19, 11), Sum.inr (14, 54),
    Sum.inr (14, 53), Sum.inr (19, 8),
    Sum.inr (21, 24), Sum.inr (16, 37),
    Sum.inr (16, 38), Sum.inr (21, 27),
    Sum.inr (15, 47), Sum.inr (18, 18),
    Sum.inr (18, 17), Sum.inr (15, 44),
    Sum.inr (15, 35), Sum.inr (18, 30),
    Sum.inr (18, 29), Sum.inr (15, 32),
    Sum.inr (21, 20), Sum.inr (16, 41),
    Sum.inr (16, 42), Sum.inr (21, 23)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket16Sign : Fin 64 → ℤ :=
  ![-1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1,
    -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1, -1, 1, 1, -1, 1, -1, -1, 1,
    -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket16Phase : Fin 64 → ZMod 2 :=
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
theorem generatedFifthXiShortPacket16_physical : ∀ e : Fin 64, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket16Source e)) i =
      2 * generatedFifthXiShortPacket16Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket16Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
