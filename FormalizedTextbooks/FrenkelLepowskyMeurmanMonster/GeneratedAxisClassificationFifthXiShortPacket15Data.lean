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
def generatedFifthXiShortPacket15Target (e : Fin 64) : generatedFifthXiShortCachedLabel :=
  Sum.inr (15, e)

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket15Source : Fin 64 → generatedFifthXiShortCachedLabel :=
  ![Sum.inr (21, 34), Sum.inr (16, 31),
    Sum.inr (16, 28), Sum.inr (21, 33),
    Sum.inr (15, 21), Sum.inr (18, 40),
    Sum.inr (18, 43), Sum.inr (15, 22),
    Sum.inr (15, 25), Sum.inr (18, 36),
    Sum.inr (18, 39), Sum.inr (15, 26),
    Sum.inr (21, 46), Sum.inr (16, 19),
    Sum.inr (16, 16), Sum.inr (21, 45),
    Sum.inr (19, 61), Sum.inr (14, 0),
    Sum.inr (14, 3), Sum.inr (19, 62),
    Sum.inr (17, 10), Sum.inr (20, 55),
    Sum.inr (20, 52), Sum.inr (17, 9),
    Sum.inr (17, 6), Sum.inr (20, 59),
    Sum.inr (20, 56), Sum.inr (17, 5),
    Sum.inr (19, 49), Sum.inr (14, 12),
    Sum.inr (14, 15), Sum.inr (19, 50),
    Sum.inr (19, 13), Sum.inr (14, 48),
    Sum.inr (14, 51), Sum.inr (19, 14),
    Sum.inr (17, 58), Sum.inr (20, 7),
    Sum.inr (20, 4), Sum.inr (17, 57),
    Sum.inr (17, 54), Sum.inr (20, 11),
    Sum.inr (20, 8), Sum.inr (17, 53),
    Sum.inr (19, 1), Sum.inr (14, 60),
    Sum.inr (14, 63), Sum.inr (19, 2),
    Sum.inr (21, 18), Sum.inr (16, 47),
    Sum.inr (16, 44), Sum.inr (21, 17),
    Sum.inr (15, 37), Sum.inr (18, 24),
    Sum.inr (18, 27), Sum.inr (15, 38),
    Sum.inr (15, 41), Sum.inr (18, 20),
    Sum.inr (18, 23), Sum.inr (15, 42),
    Sum.inr (21, 30), Sum.inr (16, 35),
    Sum.inr (16, 32), Sum.inr (21, 29)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket15Sign : Fin 64 → ℤ :=
  ![-1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1,
    -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1, -1, 1, 1, -1, 1, -1, -1, 1,
    -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket15Phase : Fin 64 → ZMod 2 :=
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
theorem generatedFifthXiShortPacket15_physical : ∀ e : Fin 64, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket15Source e)) i =
      2 * generatedFifthXiShortPacket15Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket15Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
