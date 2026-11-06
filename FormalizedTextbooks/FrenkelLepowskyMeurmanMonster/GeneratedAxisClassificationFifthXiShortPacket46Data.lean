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
def generatedFifthXiShortPacket46Target (e : Fin 64) : generatedFifthXiShortCachedLabel :=
  Sum.inr (46, e)

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket46Source : Fin 64 → generatedFifthXiShortCachedLabel :=
  ![Sum.inr (32, 0), Sum.inr (39, 61),
    Sum.inr (39, 62), Sum.inr (32, 3),
    Sum.inr (33, 55), Sum.inr (38, 10),
    Sum.inr (38, 9), Sum.inr (33, 52),
    Sum.inr (33, 59), Sum.inr (38, 6),
    Sum.inr (38, 5), Sum.inr (33, 56),
    Sum.inr (32, 12), Sum.inr (39, 49),
    Sum.inr (39, 50), Sum.inr (32, 15),
    Sum.inr (40, 31), Sum.inr (47, 34),
    Sum.inr (47, 33), Sum.inr (40, 28),
    Sum.inr (41, 40), Sum.inr (46, 21),
    Sum.inr (46, 22), Sum.inr (41, 43),
    Sum.inr (41, 36), Sum.inr (46, 25),
    Sum.inr (46, 26), Sum.inr (41, 39),
    Sum.inr (40, 19), Sum.inr (47, 46),
    Sum.inr (47, 45), Sum.inr (40, 16),
    Sum.inr (40, 47), Sum.inr (47, 18),
    Sum.inr (47, 17), Sum.inr (40, 44),
    Sum.inr (41, 24), Sum.inr (46, 37),
    Sum.inr (46, 38), Sum.inr (41, 27),
    Sum.inr (41, 20), Sum.inr (46, 41),
    Sum.inr (46, 42), Sum.inr (41, 23),
    Sum.inr (40, 35), Sum.inr (47, 30),
    Sum.inr (47, 29), Sum.inr (40, 32),
    Sum.inr (32, 48), Sum.inr (39, 13),
    Sum.inr (39, 14), Sum.inr (32, 51),
    Sum.inr (33, 7), Sum.inr (38, 58),
    Sum.inr (38, 57), Sum.inr (33, 4),
    Sum.inr (33, 11), Sum.inr (38, 54),
    Sum.inr (38, 53), Sum.inr (33, 8),
    Sum.inr (32, 60), Sum.inr (39, 1),
    Sum.inr (39, 2), Sum.inr (32, 63)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket46Sign : Fin 64 → ℤ :=
  ![-1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1,
    -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1, -1, 1, 1, -1, 1, -1, -1, 1,
    -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket46Phase : Fin 64 → ZMod 2 :=
  ![1, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0,
    0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1,
    0, 0, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0,
    0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1,
    0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1,
    1, 1, 1, 0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Check 64 genuine source/target vectors in all 24 physical coordinates.
/-- Every displayed physical source has the asserted exact integer Xi image. -/
theorem generatedFifthXiShortPacket46_physical : ∀ e : Fin 64, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket46Source e)) i =
      2 * generatedFifthXiShortPacket46Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket46Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
