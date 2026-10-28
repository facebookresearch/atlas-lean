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
def generatedFifthXiShortPacket05Target (e : Fin 64) : generatedFifthXiShortCachedLabel :=
  Sum.inr (5, e)

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket05Source : Fin 64 → generatedFifthXiShortCachedLabel :=
  ![Sum.inr (2, 55), Sum.inr (9, 10),
    Sum.inr (9, 9), Sum.inr (2, 52),
    Sum.inr (7, 0), Sum.inr (4, 61),
    Sum.inr (4, 62), Sum.inr (7, 3),
    Sum.inr (7, 12), Sum.inr (4, 49),
    Sum.inr (4, 50), Sum.inr (7, 15),
    Sum.inr (2, 59), Sum.inr (9, 6),
    Sum.inr (9, 5), Sum.inr (2, 56),
    Sum.inr (6, 40), Sum.inr (5, 21),
    Sum.inr (5, 22), Sum.inr (6, 43),
    Sum.inr (3, 31), Sum.inr (8, 34),
    Sum.inr (8, 33), Sum.inr (3, 28),
    Sum.inr (3, 19), Sum.inr (8, 46),
    Sum.inr (8, 45), Sum.inr (3, 16),
    Sum.inr (6, 36), Sum.inr (5, 25),
    Sum.inr (5, 26), Sum.inr (6, 39),
    Sum.inr (6, 24), Sum.inr (5, 37),
    Sum.inr (5, 38), Sum.inr (6, 27),
    Sum.inr (3, 47), Sum.inr (8, 18),
    Sum.inr (8, 17), Sum.inr (3, 44),
    Sum.inr (3, 35), Sum.inr (8, 30),
    Sum.inr (8, 29), Sum.inr (3, 32),
    Sum.inr (6, 20), Sum.inr (5, 41),
    Sum.inr (5, 42), Sum.inr (6, 23),
    Sum.inr (2, 7), Sum.inr (9, 58),
    Sum.inr (9, 57), Sum.inr (2, 4),
    Sum.inr (7, 48), Sum.inr (4, 13),
    Sum.inr (4, 14), Sum.inr (7, 51),
    Sum.inr (7, 60), Sum.inr (4, 1),
    Sum.inr (4, 2), Sum.inr (7, 63),
    Sum.inr (2, 11), Sum.inr (9, 54),
    Sum.inr (9, 53), Sum.inr (2, 8)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket05Sign : Fin 64 → ℤ :=
  ![1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1,
    1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1, 1, -1, -1, 1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket05Phase : Fin 64 → ZMod 2 :=
  ![0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0,
    1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0,
    1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0,
    1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1,
    1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1,
    0, 1, 1, 1]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Check 64 genuine source/target vectors in all 24 physical coordinates.
/-- Every displayed physical source has the asserted exact integer Xi image. -/
theorem generatedFifthXiShortPacket05_physical : ∀ e : Fin 64, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket05Source e)) i =
      2 * generatedFifthXiShortPacket05Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket05Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
