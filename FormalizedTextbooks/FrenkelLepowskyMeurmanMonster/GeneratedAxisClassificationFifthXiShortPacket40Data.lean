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
def generatedFifthXiShortPacket40Target (e : Fin 64) : generatedFifthXiShortCachedLabel :=
  Sum.inr (40, e)

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket40Source : Fin 64 → generatedFifthXiShortCachedLabel :=
  ![Sum.inr (32, 10), Sum.inr (39, 55),
    Sum.inr (39, 52), Sum.inr (32, 9),
    Sum.inr (33, 61), Sum.inr (38, 0),
    Sum.inr (38, 3), Sum.inr (33, 62),
    Sum.inr (33, 49), Sum.inr (38, 12),
    Sum.inr (38, 15), Sum.inr (33, 50),
    Sum.inr (32, 6), Sum.inr (39, 59),
    Sum.inr (39, 56), Sum.inr (32, 5),
    Sum.inr (40, 21), Sum.inr (47, 40),
    Sum.inr (47, 43), Sum.inr (40, 22),
    Sum.inr (41, 34), Sum.inr (46, 31),
    Sum.inr (46, 28), Sum.inr (41, 33),
    Sum.inr (41, 46), Sum.inr (46, 19),
    Sum.inr (46, 16), Sum.inr (41, 45),
    Sum.inr (40, 25), Sum.inr (47, 36),
    Sum.inr (47, 39), Sum.inr (40, 26),
    Sum.inr (40, 37), Sum.inr (47, 24),
    Sum.inr (47, 27), Sum.inr (40, 38),
    Sum.inr (41, 18), Sum.inr (46, 47),
    Sum.inr (46, 44), Sum.inr (41, 17),
    Sum.inr (41, 30), Sum.inr (46, 35),
    Sum.inr (46, 32), Sum.inr (41, 29),
    Sum.inr (40, 41), Sum.inr (47, 20),
    Sum.inr (47, 23), Sum.inr (40, 42),
    Sum.inr (32, 58), Sum.inr (39, 7),
    Sum.inr (39, 4), Sum.inr (32, 57),
    Sum.inr (33, 13), Sum.inr (38, 48),
    Sum.inr (38, 51), Sum.inr (33, 14),
    Sum.inr (33, 1), Sum.inr (38, 60),
    Sum.inr (38, 63), Sum.inr (33, 2),
    Sum.inr (32, 54), Sum.inr (39, 11),
    Sum.inr (39, 8), Sum.inr (32, 53)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket40Sign : Fin 64 → ℤ :=
  ![-1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1,
    -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1, -1, 1, 1, -1, 1, -1, -1, 1,
    -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket40Phase : Fin 64 → ZMod 2 :=
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
theorem generatedFifthXiShortPacket40_physical : ∀ e : Fin 64, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket40Source e)) i =
      2 * generatedFifthXiShortPacket40Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket40Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
