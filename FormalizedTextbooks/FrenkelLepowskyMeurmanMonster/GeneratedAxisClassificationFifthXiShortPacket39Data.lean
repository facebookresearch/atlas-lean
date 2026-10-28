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
def generatedFifthXiShortPacket39Target (e : Fin 64) : generatedFifthXiShortCachedLabel :=
  Sum.inr (39, e)

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket39Source : Fin 64 → generatedFifthXiShortCachedLabel :=
  ![Sum.inr (32, 40), Sum.inr (39, 21),
    Sum.inr (39, 22), Sum.inr (32, 43),
    Sum.inr (33, 31), Sum.inr (38, 34),
    Sum.inr (38, 33), Sum.inr (33, 28),
    Sum.inr (33, 19), Sum.inr (38, 46),
    Sum.inr (38, 45), Sum.inr (33, 16),
    Sum.inr (32, 36), Sum.inr (39, 25),
    Sum.inr (39, 26), Sum.inr (32, 39),
    Sum.inr (40, 55), Sum.inr (47, 10),
    Sum.inr (47, 9), Sum.inr (40, 52),
    Sum.inr (41, 0), Sum.inr (46, 61),
    Sum.inr (46, 62), Sum.inr (41, 3),
    Sum.inr (41, 12), Sum.inr (46, 49),
    Sum.inr (46, 50), Sum.inr (41, 15),
    Sum.inr (40, 59), Sum.inr (47, 6),
    Sum.inr (47, 5), Sum.inr (40, 56),
    Sum.inr (40, 7), Sum.inr (47, 58),
    Sum.inr (47, 57), Sum.inr (40, 4),
    Sum.inr (41, 48), Sum.inr (46, 13),
    Sum.inr (46, 14), Sum.inr (41, 51),
    Sum.inr (41, 60), Sum.inr (46, 1),
    Sum.inr (46, 2), Sum.inr (41, 63),
    Sum.inr (40, 11), Sum.inr (47, 54),
    Sum.inr (47, 53), Sum.inr (40, 8),
    Sum.inr (32, 24), Sum.inr (39, 37),
    Sum.inr (39, 38), Sum.inr (32, 27),
    Sum.inr (33, 47), Sum.inr (38, 18),
    Sum.inr (38, 17), Sum.inr (33, 44),
    Sum.inr (33, 35), Sum.inr (38, 30),
    Sum.inr (38, 29), Sum.inr (33, 32),
    Sum.inr (32, 20), Sum.inr (39, 41),
    Sum.inr (39, 42), Sum.inr (32, 23)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket39Sign : Fin 64 → ℤ :=
  ![-1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1,
    -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1, -1, 1, 1, -1, 1, -1, -1, 1,
    -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket39Phase : Fin 64 → ZMod 2 :=
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
theorem generatedFifthXiShortPacket39_physical : ∀ e : Fin 64, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket39Source e)) i =
      2 * generatedFifthXiShortPacket39Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket39Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
