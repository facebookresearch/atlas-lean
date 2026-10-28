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
def generatedFifthXiShortPacket54Target (e : Fin 64) : generatedFifthXiShortCachedLabel :=
  Sum.inr (54, e)

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket54Source : Fin 64 → generatedFifthXiShortCachedLabel :=
  ![Sum.inr (24, 34), Sum.inr (48, 31),
    Sum.inr (48, 28), Sum.inr (24, 33),
    Sum.inr (54, 21), Sum.inr (30, 40),
    Sum.inr (30, 43), Sum.inr (54, 22),
    Sum.inr (54, 25), Sum.inr (30, 36),
    Sum.inr (30, 39), Sum.inr (54, 26),
    Sum.inr (24, 46), Sum.inr (48, 19),
    Sum.inr (48, 16), Sum.inr (24, 45),
    Sum.inr (55, 61), Sum.inr (31, 0),
    Sum.inr (31, 3), Sum.inr (55, 62),
    Sum.inr (25, 10), Sum.inr (49, 55),
    Sum.inr (49, 52), Sum.inr (25, 9),
    Sum.inr (25, 6), Sum.inr (49, 59),
    Sum.inr (49, 56), Sum.inr (25, 5),
    Sum.inr (55, 49), Sum.inr (31, 12),
    Sum.inr (31, 15), Sum.inr (55, 50),
    Sum.inr (55, 13), Sum.inr (31, 48),
    Sum.inr (31, 51), Sum.inr (55, 14),
    Sum.inr (25, 58), Sum.inr (49, 7),
    Sum.inr (49, 4), Sum.inr (25, 57),
    Sum.inr (25, 54), Sum.inr (49, 11),
    Sum.inr (49, 8), Sum.inr (25, 53),
    Sum.inr (55, 1), Sum.inr (31, 60),
    Sum.inr (31, 63), Sum.inr (55, 2),
    Sum.inr (24, 18), Sum.inr (48, 47),
    Sum.inr (48, 44), Sum.inr (24, 17),
    Sum.inr (54, 37), Sum.inr (30, 24),
    Sum.inr (30, 27), Sum.inr (54, 38),
    Sum.inr (54, 41), Sum.inr (30, 20),
    Sum.inr (30, 23), Sum.inr (54, 42),
    Sum.inr (24, 30), Sum.inr (48, 35),
    Sum.inr (48, 32), Sum.inr (24, 29)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket54Sign : Fin 64 → ℤ :=
  ![-1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1,
    -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1, -1, 1, 1, -1, 1, -1, -1, 1,
    -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket54Phase : Fin 64 → ZMod 2 :=
  ![0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0,
    1, 1, 1, 0, 1, 0, 0, 0, 1, 1, 1, 0,
    1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0,
    1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 1,
    1, 1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 1,
    0, 0, 0, 1]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Check 64 genuine source/target vectors in all 24 physical coordinates.
/-- Every displayed physical source has the asserted exact integer Xi image. -/
theorem generatedFifthXiShortPacket54_physical : ∀ e : Fin 64, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket54Source e)) i =
      2 * generatedFifthXiShortPacket54Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket54Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
