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
def generatedFifthXiShortPacket30Target (e : Fin 64) : generatedFifthXiShortCachedLabel :=
  Sum.inr (30, e)

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket30Source : Fin 64 → generatedFifthXiShortCachedLabel :=
  ![Sum.inr (24, 31), Sum.inr (48, 34),
    Sum.inr (48, 33), Sum.inr (24, 28),
    Sum.inr (54, 40), Sum.inr (30, 21),
    Sum.inr (30, 22), Sum.inr (54, 43),
    Sum.inr (54, 36), Sum.inr (30, 25),
    Sum.inr (30, 26), Sum.inr (54, 39),
    Sum.inr (24, 19), Sum.inr (48, 46),
    Sum.inr (48, 45), Sum.inr (24, 16),
    Sum.inr (55, 0), Sum.inr (31, 61),
    Sum.inr (31, 62), Sum.inr (55, 3),
    Sum.inr (25, 55), Sum.inr (49, 10),
    Sum.inr (49, 9), Sum.inr (25, 52),
    Sum.inr (25, 59), Sum.inr (49, 6),
    Sum.inr (49, 5), Sum.inr (25, 56),
    Sum.inr (55, 12), Sum.inr (31, 49),
    Sum.inr (31, 50), Sum.inr (55, 15),
    Sum.inr (55, 48), Sum.inr (31, 13),
    Sum.inr (31, 14), Sum.inr (55, 51),
    Sum.inr (25, 7), Sum.inr (49, 58),
    Sum.inr (49, 57), Sum.inr (25, 4),
    Sum.inr (25, 11), Sum.inr (49, 54),
    Sum.inr (49, 53), Sum.inr (25, 8),
    Sum.inr (55, 60), Sum.inr (31, 1),
    Sum.inr (31, 2), Sum.inr (55, 63),
    Sum.inr (24, 47), Sum.inr (48, 18),
    Sum.inr (48, 17), Sum.inr (24, 44),
    Sum.inr (54, 24), Sum.inr (30, 37),
    Sum.inr (30, 38), Sum.inr (54, 27),
    Sum.inr (54, 20), Sum.inr (30, 41),
    Sum.inr (30, 42), Sum.inr (54, 23),
    Sum.inr (24, 35), Sum.inr (48, 30),
    Sum.inr (48, 29), Sum.inr (24, 32)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket30Sign : Fin 64 → ℤ :=
  ![1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1,
    1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1, 1, -1, -1, 1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket30Phase : Fin 64 → ZMod 2 :=
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
theorem generatedFifthXiShortPacket30_physical : ∀ e : Fin 64, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket30Source e)) i =
      2 * generatedFifthXiShortPacket30Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket30Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
