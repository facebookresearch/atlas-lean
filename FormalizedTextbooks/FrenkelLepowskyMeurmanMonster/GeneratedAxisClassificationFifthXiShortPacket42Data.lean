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
def generatedFifthXiShortPacket42Target (e : Fin 64) : generatedFifthXiShortCachedLabel :=
  Sum.inr (42, e)

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket42Source : Fin 64 → generatedFifthXiShortCachedLabel :=
  ![Sum.inr (37, 55), Sum.inr (34, 10),
    Sum.inr (34, 9), Sum.inr (37, 52),
    Sum.inr (36, 0), Sum.inr (35, 61),
    Sum.inr (35, 62), Sum.inr (36, 3),
    Sum.inr (36, 12), Sum.inr (35, 49),
    Sum.inr (35, 50), Sum.inr (36, 15),
    Sum.inr (37, 59), Sum.inr (34, 6),
    Sum.inr (34, 5), Sum.inr (37, 56),
    Sum.inr (45, 40), Sum.inr (42, 21),
    Sum.inr (42, 22), Sum.inr (45, 43),
    Sum.inr (44, 31), Sum.inr (43, 34),
    Sum.inr (43, 33), Sum.inr (44, 28),
    Sum.inr (44, 19), Sum.inr (43, 46),
    Sum.inr (43, 45), Sum.inr (44, 16),
    Sum.inr (45, 36), Sum.inr (42, 25),
    Sum.inr (42, 26), Sum.inr (45, 39),
    Sum.inr (45, 24), Sum.inr (42, 37),
    Sum.inr (42, 38), Sum.inr (45, 27),
    Sum.inr (44, 47), Sum.inr (43, 18),
    Sum.inr (43, 17), Sum.inr (44, 44),
    Sum.inr (44, 35), Sum.inr (43, 30),
    Sum.inr (43, 29), Sum.inr (44, 32),
    Sum.inr (45, 20), Sum.inr (42, 41),
    Sum.inr (42, 42), Sum.inr (45, 23),
    Sum.inr (37, 7), Sum.inr (34, 58),
    Sum.inr (34, 57), Sum.inr (37, 4),
    Sum.inr (36, 48), Sum.inr (35, 13),
    Sum.inr (35, 14), Sum.inr (36, 51),
    Sum.inr (36, 60), Sum.inr (35, 1),
    Sum.inr (35, 2), Sum.inr (36, 63),
    Sum.inr (37, 11), Sum.inr (34, 54),
    Sum.inr (34, 53), Sum.inr (37, 8)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket42Sign : Fin 64 → ℤ :=
  ![1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1,
    1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1, 1, -1, -1, 1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket42Phase : Fin 64 → ZMod 2 :=
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
theorem generatedFifthXiShortPacket42_physical : ∀ e : Fin 64, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket42Source e)) i =
      2 * generatedFifthXiShortPacket42Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket42Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
