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
def generatedFifthXiShortPacket17Target (e : Fin 64) : generatedFifthXiShortCachedLabel :=
  Sum.inr (17, e)

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket17Source : Fin 64 → generatedFifthXiShortCachedLabel :=
  ![Sum.inr (21, 61), Sum.inr (16, 0),
    Sum.inr (16, 3), Sum.inr (21, 62),
    Sum.inr (15, 10), Sum.inr (18, 55),
    Sum.inr (18, 52), Sum.inr (15, 9),
    Sum.inr (15, 6), Sum.inr (18, 59),
    Sum.inr (18, 56), Sum.inr (15, 5),
    Sum.inr (21, 49), Sum.inr (16, 12),
    Sum.inr (16, 15), Sum.inr (21, 50),
    Sum.inr (19, 34), Sum.inr (14, 31),
    Sum.inr (14, 28), Sum.inr (19, 33),
    Sum.inr (17, 21), Sum.inr (20, 40),
    Sum.inr (20, 43), Sum.inr (17, 22),
    Sum.inr (17, 25), Sum.inr (20, 36),
    Sum.inr (20, 39), Sum.inr (17, 26),
    Sum.inr (19, 46), Sum.inr (14, 19),
    Sum.inr (14, 16), Sum.inr (19, 45),
    Sum.inr (19, 18), Sum.inr (14, 47),
    Sum.inr (14, 44), Sum.inr (19, 17),
    Sum.inr (17, 37), Sum.inr (20, 24),
    Sum.inr (20, 27), Sum.inr (17, 38),
    Sum.inr (17, 41), Sum.inr (20, 20),
    Sum.inr (20, 23), Sum.inr (17, 42),
    Sum.inr (19, 30), Sum.inr (14, 35),
    Sum.inr (14, 32), Sum.inr (19, 29),
    Sum.inr (21, 13), Sum.inr (16, 48),
    Sum.inr (16, 51), Sum.inr (21, 14),
    Sum.inr (15, 58), Sum.inr (18, 7),
    Sum.inr (18, 4), Sum.inr (15, 57),
    Sum.inr (15, 54), Sum.inr (18, 11),
    Sum.inr (18, 8), Sum.inr (15, 53),
    Sum.inr (21, 1), Sum.inr (16, 60),
    Sum.inr (16, 63), Sum.inr (21, 2)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket17Sign : Fin 64 → ℤ :=
  ![1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1,
    1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1, 1, -1, -1, 1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket17Phase : Fin 64 → ZMod 2 :=
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
theorem generatedFifthXiShortPacket17_physical : ∀ e : Fin 64, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket17Source e)) i =
      2 * generatedFifthXiShortPacket17Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket17Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
