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
def generatedFifthXiShortPacket24Target (e : Fin 64) : generatedFifthXiShortCachedLabel :=
  Sum.inr (24, e)

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket24Source : Fin 64 → generatedFifthXiShortCachedLabel :=
  ![Sum.inr (24, 21), Sum.inr (48, 40),
    Sum.inr (48, 43), Sum.inr (24, 22),
    Sum.inr (54, 34), Sum.inr (30, 31),
    Sum.inr (30, 28), Sum.inr (54, 33),
    Sum.inr (54, 46), Sum.inr (30, 19),
    Sum.inr (30, 16), Sum.inr (54, 45),
    Sum.inr (24, 25), Sum.inr (48, 36),
    Sum.inr (48, 39), Sum.inr (24, 26),
    Sum.inr (55, 10), Sum.inr (31, 55),
    Sum.inr (31, 52), Sum.inr (55, 9),
    Sum.inr (25, 61), Sum.inr (49, 0),
    Sum.inr (49, 3), Sum.inr (25, 62),
    Sum.inr (25, 49), Sum.inr (49, 12),
    Sum.inr (49, 15), Sum.inr (25, 50),
    Sum.inr (55, 6), Sum.inr (31, 59),
    Sum.inr (31, 56), Sum.inr (55, 5),
    Sum.inr (55, 58), Sum.inr (31, 7),
    Sum.inr (31, 4), Sum.inr (55, 57),
    Sum.inr (25, 13), Sum.inr (49, 48),
    Sum.inr (49, 51), Sum.inr (25, 14),
    Sum.inr (25, 1), Sum.inr (49, 60),
    Sum.inr (49, 63), Sum.inr (25, 2),
    Sum.inr (55, 54), Sum.inr (31, 11),
    Sum.inr (31, 8), Sum.inr (55, 53),
    Sum.inr (24, 37), Sum.inr (48, 24),
    Sum.inr (48, 27), Sum.inr (24, 38),
    Sum.inr (54, 18), Sum.inr (30, 47),
    Sum.inr (30, 44), Sum.inr (54, 17),
    Sum.inr (54, 30), Sum.inr (30, 35),
    Sum.inr (30, 32), Sum.inr (54, 29),
    Sum.inr (24, 41), Sum.inr (48, 20),
    Sum.inr (48, 23), Sum.inr (24, 42)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket24Sign : Fin 64 → ℤ :=
  ![1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1,
    1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1, 1, -1, -1, 1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket24Phase : Fin 64 → ZMod 2 :=
  ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1,
    0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 0,
    1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0,
    1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1,
    0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0,
    1, 0, 0, 0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Check 64 genuine source/target vectors in all 24 physical coordinates.
/-- Every displayed physical source has the asserted exact integer Xi image. -/
theorem generatedFifthXiShortPacket24_physical : ∀ e : Fin 64, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket24Source e)) i =
      2 * generatedFifthXiShortPacket24Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket24Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
