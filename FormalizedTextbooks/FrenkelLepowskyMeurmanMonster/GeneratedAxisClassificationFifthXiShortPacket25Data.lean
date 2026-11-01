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
def generatedFifthXiShortPacket25Target (e : Fin 64) : generatedFifthXiShortCachedLabel :=
  Sum.inr (25, e)

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket25Source : Fin 64 → generatedFifthXiShortCachedLabel :=
  ![Sum.inr (24, 61), Sum.inr (48, 0),
    Sum.inr (48, 3), Sum.inr (24, 62),
    Sum.inr (54, 10), Sum.inr (30, 55),
    Sum.inr (30, 52), Sum.inr (54, 9),
    Sum.inr (54, 6), Sum.inr (30, 59),
    Sum.inr (30, 56), Sum.inr (54, 5),
    Sum.inr (24, 49), Sum.inr (48, 12),
    Sum.inr (48, 15), Sum.inr (24, 50),
    Sum.inr (55, 34), Sum.inr (31, 31),
    Sum.inr (31, 28), Sum.inr (55, 33),
    Sum.inr (25, 21), Sum.inr (49, 40),
    Sum.inr (49, 43), Sum.inr (25, 22),
    Sum.inr (25, 25), Sum.inr (49, 36),
    Sum.inr (49, 39), Sum.inr (25, 26),
    Sum.inr (55, 46), Sum.inr (31, 19),
    Sum.inr (31, 16), Sum.inr (55, 45),
    Sum.inr (55, 18), Sum.inr (31, 47),
    Sum.inr (31, 44), Sum.inr (55, 17),
    Sum.inr (25, 37), Sum.inr (49, 24),
    Sum.inr (49, 27), Sum.inr (25, 38),
    Sum.inr (25, 41), Sum.inr (49, 20),
    Sum.inr (49, 23), Sum.inr (25, 42),
    Sum.inr (55, 30), Sum.inr (31, 35),
    Sum.inr (31, 32), Sum.inr (55, 29),
    Sum.inr (24, 13), Sum.inr (48, 48),
    Sum.inr (48, 51), Sum.inr (24, 14),
    Sum.inr (54, 58), Sum.inr (30, 7),
    Sum.inr (30, 4), Sum.inr (54, 57),
    Sum.inr (54, 54), Sum.inr (30, 11),
    Sum.inr (30, 8), Sum.inr (54, 53),
    Sum.inr (24, 1), Sum.inr (48, 60),
    Sum.inr (48, 63), Sum.inr (24, 2)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket25Sign : Fin 64 → ℤ :=
  ![1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1,
    1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1, 1, -1, -1, 1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket25Phase : Fin 64 → ZMod 2 :=
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
theorem generatedFifthXiShortPacket25_physical : ∀ e : Fin 64, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket25Source e)) i =
      2 * generatedFifthXiShortPacket25Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket25Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
