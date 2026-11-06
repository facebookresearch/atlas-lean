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
def generatedFifthXiShortPacket04Target (e : Fin 64) : generatedFifthXiShortCachedLabel :=
  Sum.inr (4, e)

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket04Source : Fin 64 → generatedFifthXiShortCachedLabel :=
  ![Sum.inr (2, 31), Sum.inr (9, 34),
    Sum.inr (9, 33), Sum.inr (2, 28),
    Sum.inr (7, 40), Sum.inr (4, 21),
    Sum.inr (4, 22), Sum.inr (7, 43),
    Sum.inr (7, 36), Sum.inr (4, 25),
    Sum.inr (4, 26), Sum.inr (7, 39),
    Sum.inr (2, 19), Sum.inr (9, 46),
    Sum.inr (9, 45), Sum.inr (2, 16),
    Sum.inr (6, 0), Sum.inr (5, 61),
    Sum.inr (5, 62), Sum.inr (6, 3),
    Sum.inr (3, 55), Sum.inr (8, 10),
    Sum.inr (8, 9), Sum.inr (3, 52),
    Sum.inr (3, 59), Sum.inr (8, 6),
    Sum.inr (8, 5), Sum.inr (3, 56),
    Sum.inr (6, 12), Sum.inr (5, 49),
    Sum.inr (5, 50), Sum.inr (6, 15),
    Sum.inr (6, 48), Sum.inr (5, 13),
    Sum.inr (5, 14), Sum.inr (6, 51),
    Sum.inr (3, 7), Sum.inr (8, 58),
    Sum.inr (8, 57), Sum.inr (3, 4),
    Sum.inr (3, 11), Sum.inr (8, 54),
    Sum.inr (8, 53), Sum.inr (3, 8),
    Sum.inr (6, 60), Sum.inr (5, 1),
    Sum.inr (5, 2), Sum.inr (6, 63),
    Sum.inr (2, 47), Sum.inr (9, 18),
    Sum.inr (9, 17), Sum.inr (2, 44),
    Sum.inr (7, 24), Sum.inr (4, 37),
    Sum.inr (4, 38), Sum.inr (7, 27),
    Sum.inr (7, 20), Sum.inr (4, 41),
    Sum.inr (4, 42), Sum.inr (7, 23),
    Sum.inr (2, 35), Sum.inr (9, 30),
    Sum.inr (9, 29), Sum.inr (2, 32)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket04Sign : Fin 64 → ℤ :=
  ![1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1,
    1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1, 1, -1, -1, 1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket04Phase : Fin 64 → ZMod 2 :=
  ![0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1,
    1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0,
    1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1,
    1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0,
    1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 0,
    0, 1, 1, 1]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Check 64 genuine source/target vectors in all 24 physical coordinates.
/-- Every displayed physical source has the asserted exact integer Xi image. -/
theorem generatedFifthXiShortPacket04_physical : ∀ e : Fin 64, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket04Source e)) i =
      2 * generatedFifthXiShortPacket04Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket04Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
