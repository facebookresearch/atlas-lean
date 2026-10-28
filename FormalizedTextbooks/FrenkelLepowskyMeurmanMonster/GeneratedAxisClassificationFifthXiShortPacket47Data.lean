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
def generatedFifthXiShortPacket47Target (e : Fin 64) : generatedFifthXiShortCachedLabel :=
  Sum.inr (47, e)

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket47Source : Fin 64 → generatedFifthXiShortCachedLabel :=
  ![Sum.inr (32, 55), Sum.inr (39, 10),
    Sum.inr (39, 9), Sum.inr (32, 52),
    Sum.inr (33, 0), Sum.inr (38, 61),
    Sum.inr (38, 62), Sum.inr (33, 3),
    Sum.inr (33, 12), Sum.inr (38, 49),
    Sum.inr (38, 50), Sum.inr (33, 15),
    Sum.inr (32, 59), Sum.inr (39, 6),
    Sum.inr (39, 5), Sum.inr (32, 56),
    Sum.inr (40, 40), Sum.inr (47, 21),
    Sum.inr (47, 22), Sum.inr (40, 43),
    Sum.inr (41, 31), Sum.inr (46, 34),
    Sum.inr (46, 33), Sum.inr (41, 28),
    Sum.inr (41, 19), Sum.inr (46, 46),
    Sum.inr (46, 45), Sum.inr (41, 16),
    Sum.inr (40, 36), Sum.inr (47, 25),
    Sum.inr (47, 26), Sum.inr (40, 39),
    Sum.inr (40, 24), Sum.inr (47, 37),
    Sum.inr (47, 38), Sum.inr (40, 27),
    Sum.inr (41, 47), Sum.inr (46, 18),
    Sum.inr (46, 17), Sum.inr (41, 44),
    Sum.inr (41, 35), Sum.inr (46, 30),
    Sum.inr (46, 29), Sum.inr (41, 32),
    Sum.inr (40, 20), Sum.inr (47, 41),
    Sum.inr (47, 42), Sum.inr (40, 23),
    Sum.inr (32, 7), Sum.inr (39, 58),
    Sum.inr (39, 57), Sum.inr (32, 4),
    Sum.inr (33, 48), Sum.inr (38, 13),
    Sum.inr (38, 14), Sum.inr (33, 51),
    Sum.inr (33, 60), Sum.inr (38, 1),
    Sum.inr (38, 2), Sum.inr (33, 63),
    Sum.inr (32, 11), Sum.inr (39, 54),
    Sum.inr (39, 53), Sum.inr (32, 8)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket47Sign : Fin 64 → ℤ :=
  ![1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1,
    1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1, 1, -1, -1, 1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket47Phase : Fin 64 → ZMod 2 :=
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
theorem generatedFifthXiShortPacket47_physical : ∀ e : Fin 64, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket47Source e)) i =
      2 * generatedFifthXiShortPacket47Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket47Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
