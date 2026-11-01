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
def generatedFifthXiShortPacket41Target (e : Fin 64) : generatedFifthXiShortCachedLabel :=
  Sum.inr (41, e)

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket41Source : Fin 64 → generatedFifthXiShortCachedLabel :=
  ![Sum.inr (32, 61), Sum.inr (39, 0),
    Sum.inr (39, 3), Sum.inr (32, 62),
    Sum.inr (33, 10), Sum.inr (38, 55),
    Sum.inr (38, 52), Sum.inr (33, 9),
    Sum.inr (33, 6), Sum.inr (38, 59),
    Sum.inr (38, 56), Sum.inr (33, 5),
    Sum.inr (32, 49), Sum.inr (39, 12),
    Sum.inr (39, 15), Sum.inr (32, 50),
    Sum.inr (40, 34), Sum.inr (47, 31),
    Sum.inr (47, 28), Sum.inr (40, 33),
    Sum.inr (41, 21), Sum.inr (46, 40),
    Sum.inr (46, 43), Sum.inr (41, 22),
    Sum.inr (41, 25), Sum.inr (46, 36),
    Sum.inr (46, 39), Sum.inr (41, 26),
    Sum.inr (40, 46), Sum.inr (47, 19),
    Sum.inr (47, 16), Sum.inr (40, 45),
    Sum.inr (40, 18), Sum.inr (47, 47),
    Sum.inr (47, 44), Sum.inr (40, 17),
    Sum.inr (41, 37), Sum.inr (46, 24),
    Sum.inr (46, 27), Sum.inr (41, 38),
    Sum.inr (41, 41), Sum.inr (46, 20),
    Sum.inr (46, 23), Sum.inr (41, 42),
    Sum.inr (40, 30), Sum.inr (47, 35),
    Sum.inr (47, 32), Sum.inr (40, 29),
    Sum.inr (32, 13), Sum.inr (39, 48),
    Sum.inr (39, 51), Sum.inr (32, 14),
    Sum.inr (33, 58), Sum.inr (38, 7),
    Sum.inr (38, 4), Sum.inr (33, 57),
    Sum.inr (33, 54), Sum.inr (38, 11),
    Sum.inr (38, 8), Sum.inr (33, 53),
    Sum.inr (32, 1), Sum.inr (39, 60),
    Sum.inr (39, 63), Sum.inr (32, 2)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket41Sign : Fin 64 → ℤ :=
  ![1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1,
    1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1, 1, -1, -1, 1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket41Phase : Fin 64 → ZMod 2 :=
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
theorem generatedFifthXiShortPacket41_physical : ∀ e : Fin 64, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket41Source e)) i =
      2 * generatedFifthXiShortPacket41Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket41Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
