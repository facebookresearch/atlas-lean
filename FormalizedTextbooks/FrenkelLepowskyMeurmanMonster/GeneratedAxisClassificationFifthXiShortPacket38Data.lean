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
def generatedFifthXiShortPacket38Target (e : Fin 64) : generatedFifthXiShortCachedLabel :=
  Sum.inr (38, e)

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket38Source : Fin 64 → generatedFifthXiShortCachedLabel :=
  ![Sum.inr (32, 31), Sum.inr (39, 34),
    Sum.inr (39, 33), Sum.inr (32, 28),
    Sum.inr (33, 40), Sum.inr (38, 21),
    Sum.inr (38, 22), Sum.inr (33, 43),
    Sum.inr (33, 36), Sum.inr (38, 25),
    Sum.inr (38, 26), Sum.inr (33, 39),
    Sum.inr (32, 19), Sum.inr (39, 46),
    Sum.inr (39, 45), Sum.inr (32, 16),
    Sum.inr (40, 0), Sum.inr (47, 61),
    Sum.inr (47, 62), Sum.inr (40, 3),
    Sum.inr (41, 55), Sum.inr (46, 10),
    Sum.inr (46, 9), Sum.inr (41, 52),
    Sum.inr (41, 59), Sum.inr (46, 6),
    Sum.inr (46, 5), Sum.inr (41, 56),
    Sum.inr (40, 12), Sum.inr (47, 49),
    Sum.inr (47, 50), Sum.inr (40, 15),
    Sum.inr (40, 48), Sum.inr (47, 13),
    Sum.inr (47, 14), Sum.inr (40, 51),
    Sum.inr (41, 7), Sum.inr (46, 58),
    Sum.inr (46, 57), Sum.inr (41, 4),
    Sum.inr (41, 11), Sum.inr (46, 54),
    Sum.inr (46, 53), Sum.inr (41, 8),
    Sum.inr (40, 60), Sum.inr (47, 1),
    Sum.inr (47, 2), Sum.inr (40, 63),
    Sum.inr (32, 47), Sum.inr (39, 18),
    Sum.inr (39, 17), Sum.inr (32, 44),
    Sum.inr (33, 24), Sum.inr (38, 37),
    Sum.inr (38, 38), Sum.inr (33, 27),
    Sum.inr (33, 20), Sum.inr (38, 41),
    Sum.inr (38, 42), Sum.inr (33, 23),
    Sum.inr (32, 35), Sum.inr (39, 30),
    Sum.inr (39, 29), Sum.inr (32, 32)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket38Sign : Fin 64 → ℤ :=
  ![1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1,
    1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1, 1, -1, -1, 1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket38Phase : Fin 64 → ZMod 2 :=
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
theorem generatedFifthXiShortPacket38_physical : ∀ e : Fin 64, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket38Source e)) i =
      2 * generatedFifthXiShortPacket38Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket38Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
