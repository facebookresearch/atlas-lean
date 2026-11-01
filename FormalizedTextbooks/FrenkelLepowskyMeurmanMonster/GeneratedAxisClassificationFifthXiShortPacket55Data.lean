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
def generatedFifthXiShortPacket55Target (e : Fin 64) : generatedFifthXiShortCachedLabel :=
  Sum.inr (55, e)

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket55Source : Fin 64 → generatedFifthXiShortCachedLabel :=
  ![Sum.inr (24, 10), Sum.inr (48, 55),
    Sum.inr (48, 52), Sum.inr (24, 9),
    Sum.inr (54, 61), Sum.inr (30, 0),
    Sum.inr (30, 3), Sum.inr (54, 62),
    Sum.inr (54, 49), Sum.inr (30, 12),
    Sum.inr (30, 15), Sum.inr (54, 50),
    Sum.inr (24, 6), Sum.inr (48, 59),
    Sum.inr (48, 56), Sum.inr (24, 5),
    Sum.inr (55, 21), Sum.inr (31, 40),
    Sum.inr (31, 43), Sum.inr (55, 22),
    Sum.inr (25, 34), Sum.inr (49, 31),
    Sum.inr (49, 28), Sum.inr (25, 33),
    Sum.inr (25, 46), Sum.inr (49, 19),
    Sum.inr (49, 16), Sum.inr (25, 45),
    Sum.inr (55, 25), Sum.inr (31, 36),
    Sum.inr (31, 39), Sum.inr (55, 26),
    Sum.inr (55, 37), Sum.inr (31, 24),
    Sum.inr (31, 27), Sum.inr (55, 38),
    Sum.inr (25, 18), Sum.inr (49, 47),
    Sum.inr (49, 44), Sum.inr (25, 17),
    Sum.inr (25, 30), Sum.inr (49, 35),
    Sum.inr (49, 32), Sum.inr (25, 29),
    Sum.inr (55, 41), Sum.inr (31, 20),
    Sum.inr (31, 23), Sum.inr (55, 42),
    Sum.inr (24, 58), Sum.inr (48, 7),
    Sum.inr (48, 4), Sum.inr (24, 57),
    Sum.inr (54, 13), Sum.inr (30, 48),
    Sum.inr (30, 51), Sum.inr (54, 14),
    Sum.inr (54, 1), Sum.inr (30, 60),
    Sum.inr (30, 63), Sum.inr (54, 2),
    Sum.inr (24, 54), Sum.inr (48, 11),
    Sum.inr (48, 8), Sum.inr (24, 53)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket55Sign : Fin 64 → ℤ :=
  ![-1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1,
    -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1, -1, 1, 1, -1, 1, -1, -1, 1,
    -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket55Phase : Fin 64 → ZMod 2 :=
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
theorem generatedFifthXiShortPacket55_physical : ∀ e : Fin 64, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket55Source e)) i =
      2 * generatedFifthXiShortPacket55Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket55Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
