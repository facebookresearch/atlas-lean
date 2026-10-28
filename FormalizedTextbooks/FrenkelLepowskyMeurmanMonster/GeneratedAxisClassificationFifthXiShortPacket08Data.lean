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
def generatedFifthXiShortPacket08Target (e : Fin 64) : generatedFifthXiShortCachedLabel :=
  Sum.inr (8, e)

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket08Source : Fin 64 → generatedFifthXiShortCachedLabel :=
  ![Sum.inr (2, 0), Sum.inr (9, 61),
    Sum.inr (9, 62), Sum.inr (2, 3),
    Sum.inr (7, 55), Sum.inr (4, 10),
    Sum.inr (4, 9), Sum.inr (7, 52),
    Sum.inr (7, 59), Sum.inr (4, 6),
    Sum.inr (4, 5), Sum.inr (7, 56),
    Sum.inr (2, 12), Sum.inr (9, 49),
    Sum.inr (9, 50), Sum.inr (2, 15),
    Sum.inr (6, 31), Sum.inr (5, 34),
    Sum.inr (5, 33), Sum.inr (6, 28),
    Sum.inr (3, 40), Sum.inr (8, 21),
    Sum.inr (8, 22), Sum.inr (3, 43),
    Sum.inr (3, 36), Sum.inr (8, 25),
    Sum.inr (8, 26), Sum.inr (3, 39),
    Sum.inr (6, 19), Sum.inr (5, 46),
    Sum.inr (5, 45), Sum.inr (6, 16),
    Sum.inr (6, 47), Sum.inr (5, 18),
    Sum.inr (5, 17), Sum.inr (6, 44),
    Sum.inr (3, 24), Sum.inr (8, 37),
    Sum.inr (8, 38), Sum.inr (3, 27),
    Sum.inr (3, 20), Sum.inr (8, 41),
    Sum.inr (8, 42), Sum.inr (3, 23),
    Sum.inr (6, 35), Sum.inr (5, 30),
    Sum.inr (5, 29), Sum.inr (6, 32),
    Sum.inr (2, 48), Sum.inr (9, 13),
    Sum.inr (9, 14), Sum.inr (2, 51),
    Sum.inr (7, 7), Sum.inr (4, 58),
    Sum.inr (4, 57), Sum.inr (7, 4),
    Sum.inr (7, 11), Sum.inr (4, 54),
    Sum.inr (4, 53), Sum.inr (7, 8),
    Sum.inr (2, 60), Sum.inr (9, 1),
    Sum.inr (9, 2), Sum.inr (2, 63)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket08Sign : Fin 64 → ℤ :=
  ![-1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1,
    -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1, -1, 1, 1, -1, 1, -1, -1, 1,
    -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket08Phase : Fin 64 → ZMod 2 :=
  ![0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0,
    1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 0, 1,
    0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1,
    0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0,
    1, 1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 1,
    0, 0, 0, 1]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Check 64 genuine source/target vectors in all 24 physical coordinates.
/-- Every displayed physical source has the asserted exact integer Xi image. -/
theorem generatedFifthXiShortPacket08_physical : ∀ e : Fin 64, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket08Source e)) i =
      2 * generatedFifthXiShortPacket08Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket08Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
