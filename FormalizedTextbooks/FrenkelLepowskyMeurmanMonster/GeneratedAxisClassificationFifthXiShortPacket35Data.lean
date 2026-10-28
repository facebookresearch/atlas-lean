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
def generatedFifthXiShortPacket35Target (e : Fin 64) : generatedFifthXiShortCachedLabel :=
  Sum.inr (35, e)

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket35Source : Fin 64 → generatedFifthXiShortCachedLabel :=
  ![Sum.inr (37, 31), Sum.inr (34, 34),
    Sum.inr (34, 33), Sum.inr (37, 28),
    Sum.inr (36, 40), Sum.inr (35, 21),
    Sum.inr (35, 22), Sum.inr (36, 43),
    Sum.inr (36, 36), Sum.inr (35, 25),
    Sum.inr (35, 26), Sum.inr (36, 39),
    Sum.inr (37, 19), Sum.inr (34, 46),
    Sum.inr (34, 45), Sum.inr (37, 16),
    Sum.inr (45, 0), Sum.inr (42, 61),
    Sum.inr (42, 62), Sum.inr (45, 3),
    Sum.inr (44, 55), Sum.inr (43, 10),
    Sum.inr (43, 9), Sum.inr (44, 52),
    Sum.inr (44, 59), Sum.inr (43, 6),
    Sum.inr (43, 5), Sum.inr (44, 56),
    Sum.inr (45, 12), Sum.inr (42, 49),
    Sum.inr (42, 50), Sum.inr (45, 15),
    Sum.inr (45, 48), Sum.inr (42, 13),
    Sum.inr (42, 14), Sum.inr (45, 51),
    Sum.inr (44, 7), Sum.inr (43, 58),
    Sum.inr (43, 57), Sum.inr (44, 4),
    Sum.inr (44, 11), Sum.inr (43, 54),
    Sum.inr (43, 53), Sum.inr (44, 8),
    Sum.inr (45, 60), Sum.inr (42, 1),
    Sum.inr (42, 2), Sum.inr (45, 63),
    Sum.inr (37, 47), Sum.inr (34, 18),
    Sum.inr (34, 17), Sum.inr (37, 44),
    Sum.inr (36, 24), Sum.inr (35, 37),
    Sum.inr (35, 38), Sum.inr (36, 27),
    Sum.inr (36, 20), Sum.inr (35, 41),
    Sum.inr (35, 42), Sum.inr (36, 23),
    Sum.inr (37, 35), Sum.inr (34, 30),
    Sum.inr (34, 29), Sum.inr (37, 32)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket35Sign : Fin 64 → ℤ :=
  ![1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1,
    1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1, 1, -1, -1, 1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket35Phase : Fin 64 → ZMod 2 :=
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
theorem generatedFifthXiShortPacket35_physical : ∀ e : Fin 64, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket35Source e)) i =
      2 * generatedFifthXiShortPacket35Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket35Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
