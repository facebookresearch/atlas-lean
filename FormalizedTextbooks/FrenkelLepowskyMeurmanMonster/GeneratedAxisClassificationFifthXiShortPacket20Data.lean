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
def generatedFifthXiShortPacket20Target (e : Fin 64) : generatedFifthXiShortCachedLabel :=
  Sum.inr (20, e)

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket20Source : Fin 64 → generatedFifthXiShortCachedLabel :=
  ![Sum.inr (21, 0), Sum.inr (16, 61),
    Sum.inr (16, 62), Sum.inr (21, 3),
    Sum.inr (15, 55), Sum.inr (18, 10),
    Sum.inr (18, 9), Sum.inr (15, 52),
    Sum.inr (15, 59), Sum.inr (18, 6),
    Sum.inr (18, 5), Sum.inr (15, 56),
    Sum.inr (21, 12), Sum.inr (16, 49),
    Sum.inr (16, 50), Sum.inr (21, 15),
    Sum.inr (19, 31), Sum.inr (14, 34),
    Sum.inr (14, 33), Sum.inr (19, 28),
    Sum.inr (17, 40), Sum.inr (20, 21),
    Sum.inr (20, 22), Sum.inr (17, 43),
    Sum.inr (17, 36), Sum.inr (20, 25),
    Sum.inr (20, 26), Sum.inr (17, 39),
    Sum.inr (19, 19), Sum.inr (14, 46),
    Sum.inr (14, 45), Sum.inr (19, 16),
    Sum.inr (19, 47), Sum.inr (14, 18),
    Sum.inr (14, 17), Sum.inr (19, 44),
    Sum.inr (17, 24), Sum.inr (20, 37),
    Sum.inr (20, 38), Sum.inr (17, 27),
    Sum.inr (17, 20), Sum.inr (20, 41),
    Sum.inr (20, 42), Sum.inr (17, 23),
    Sum.inr (19, 35), Sum.inr (14, 30),
    Sum.inr (14, 29), Sum.inr (19, 32),
    Sum.inr (21, 48), Sum.inr (16, 13),
    Sum.inr (16, 14), Sum.inr (21, 51),
    Sum.inr (15, 7), Sum.inr (18, 58),
    Sum.inr (18, 57), Sum.inr (15, 4),
    Sum.inr (15, 11), Sum.inr (18, 54),
    Sum.inr (18, 53), Sum.inr (15, 8),
    Sum.inr (21, 60), Sum.inr (16, 1),
    Sum.inr (16, 2), Sum.inr (21, 63)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket20Sign : Fin 64 → ℤ :=
  ![-1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1,
    -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1, -1, 1, 1, -1, 1, -1, -1, 1,
    -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket20Phase : Fin 64 → ZMod 2 :=
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
theorem generatedFifthXiShortPacket20_physical : ∀ e : Fin 64, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket20Source e)) i =
      2 * generatedFifthXiShortPacket20Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket20Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
