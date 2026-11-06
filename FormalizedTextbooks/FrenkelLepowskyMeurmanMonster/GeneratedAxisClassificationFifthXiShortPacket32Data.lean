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
def generatedFifthXiShortPacket32Target (e : Fin 64) : generatedFifthXiShortCachedLabel :=
  Sum.inr (32, e)

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket32Source : Fin 64 → generatedFifthXiShortCachedLabel :=
  ![Sum.inr (32, 21), Sum.inr (39, 40),
    Sum.inr (39, 43), Sum.inr (32, 22),
    Sum.inr (33, 34), Sum.inr (38, 31),
    Sum.inr (38, 28), Sum.inr (33, 33),
    Sum.inr (33, 46), Sum.inr (38, 19),
    Sum.inr (38, 16), Sum.inr (33, 45),
    Sum.inr (32, 25), Sum.inr (39, 36),
    Sum.inr (39, 39), Sum.inr (32, 26),
    Sum.inr (40, 10), Sum.inr (47, 55),
    Sum.inr (47, 52), Sum.inr (40, 9),
    Sum.inr (41, 61), Sum.inr (46, 0),
    Sum.inr (46, 3), Sum.inr (41, 62),
    Sum.inr (41, 49), Sum.inr (46, 12),
    Sum.inr (46, 15), Sum.inr (41, 50),
    Sum.inr (40, 6), Sum.inr (47, 59),
    Sum.inr (47, 56), Sum.inr (40, 5),
    Sum.inr (40, 58), Sum.inr (47, 7),
    Sum.inr (47, 4), Sum.inr (40, 57),
    Sum.inr (41, 13), Sum.inr (46, 48),
    Sum.inr (46, 51), Sum.inr (41, 14),
    Sum.inr (41, 1), Sum.inr (46, 60),
    Sum.inr (46, 63), Sum.inr (41, 2),
    Sum.inr (40, 54), Sum.inr (47, 11),
    Sum.inr (47, 8), Sum.inr (40, 53),
    Sum.inr (32, 37), Sum.inr (39, 24),
    Sum.inr (39, 27), Sum.inr (32, 38),
    Sum.inr (33, 18), Sum.inr (38, 47),
    Sum.inr (38, 44), Sum.inr (33, 17),
    Sum.inr (33, 30), Sum.inr (38, 35),
    Sum.inr (38, 32), Sum.inr (33, 29),
    Sum.inr (32, 41), Sum.inr (39, 20),
    Sum.inr (39, 23), Sum.inr (32, 42)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket32Sign : Fin 64 → ℤ :=
  ![1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1,
    1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1, 1, -1, -1, 1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket32Phase : Fin 64 → ZMod 2 :=
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
theorem generatedFifthXiShortPacket32_physical : ∀ e : Fin 64, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket32Source e)) i =
      2 * generatedFifthXiShortPacket32Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket32Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
