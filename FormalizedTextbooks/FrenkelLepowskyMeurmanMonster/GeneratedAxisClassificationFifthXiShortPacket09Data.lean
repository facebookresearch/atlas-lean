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
def generatedFifthXiShortPacket09Target (e : Fin 64) : generatedFifthXiShortCachedLabel :=
  Sum.inr (9, e)

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket09Source : Fin 64 → generatedFifthXiShortCachedLabel :=
  ![Sum.inr (2, 40), Sum.inr (9, 21),
    Sum.inr (9, 22), Sum.inr (2, 43),
    Sum.inr (7, 31), Sum.inr (4, 34),
    Sum.inr (4, 33), Sum.inr (7, 28),
    Sum.inr (7, 19), Sum.inr (4, 46),
    Sum.inr (4, 45), Sum.inr (7, 16),
    Sum.inr (2, 36), Sum.inr (9, 25),
    Sum.inr (9, 26), Sum.inr (2, 39),
    Sum.inr (6, 55), Sum.inr (5, 10),
    Sum.inr (5, 9), Sum.inr (6, 52),
    Sum.inr (3, 0), Sum.inr (8, 61),
    Sum.inr (8, 62), Sum.inr (3, 3),
    Sum.inr (3, 12), Sum.inr (8, 49),
    Sum.inr (8, 50), Sum.inr (3, 15),
    Sum.inr (6, 59), Sum.inr (5, 6),
    Sum.inr (5, 5), Sum.inr (6, 56),
    Sum.inr (6, 7), Sum.inr (5, 58),
    Sum.inr (5, 57), Sum.inr (6, 4),
    Sum.inr (3, 48), Sum.inr (8, 13),
    Sum.inr (8, 14), Sum.inr (3, 51),
    Sum.inr (3, 60), Sum.inr (8, 1),
    Sum.inr (8, 2), Sum.inr (3, 63),
    Sum.inr (6, 11), Sum.inr (5, 54),
    Sum.inr (5, 53), Sum.inr (6, 8),
    Sum.inr (2, 24), Sum.inr (9, 37),
    Sum.inr (9, 38), Sum.inr (2, 27),
    Sum.inr (7, 47), Sum.inr (4, 18),
    Sum.inr (4, 17), Sum.inr (7, 44),
    Sum.inr (7, 35), Sum.inr (4, 30),
    Sum.inr (4, 29), Sum.inr (7, 32),
    Sum.inr (2, 20), Sum.inr (9, 41),
    Sum.inr (9, 42), Sum.inr (2, 23)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket09Sign : Fin 64 → ℤ :=
  ![-1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1,
    -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1, -1, 1, 1, -1, 1, -1, -1, 1,
    -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket09Phase : Fin 64 → ZMod 2 :=
  ![1, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0,
    0, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0,
    1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 1,
    1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0,
    0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1,
    1, 1, 1, 0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Check 64 genuine source/target vectors in all 24 physical coordinates.
/-- Every displayed physical source has the asserted exact integer Xi image. -/
theorem generatedFifthXiShortPacket09_physical : ∀ e : Fin 64, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket09Source e)) i =
      2 * generatedFifthXiShortPacket09Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket09Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
