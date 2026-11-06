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
def generatedFifthXiShortPacket21Target (e : Fin 64) : generatedFifthXiShortCachedLabel :=
  Sum.inr (21, e)

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket21Source : Fin 64 → generatedFifthXiShortCachedLabel :=
  ![Sum.inr (21, 21), Sum.inr (16, 40),
    Sum.inr (16, 43), Sum.inr (21, 22),
    Sum.inr (15, 34), Sum.inr (18, 31),
    Sum.inr (18, 28), Sum.inr (15, 33),
    Sum.inr (15, 46), Sum.inr (18, 19),
    Sum.inr (18, 16), Sum.inr (15, 45),
    Sum.inr (21, 25), Sum.inr (16, 36),
    Sum.inr (16, 39), Sum.inr (21, 26),
    Sum.inr (19, 10), Sum.inr (14, 55),
    Sum.inr (14, 52), Sum.inr (19, 9),
    Sum.inr (17, 61), Sum.inr (20, 0),
    Sum.inr (20, 3), Sum.inr (17, 62),
    Sum.inr (17, 49), Sum.inr (20, 12),
    Sum.inr (20, 15), Sum.inr (17, 50),
    Sum.inr (19, 6), Sum.inr (14, 59),
    Sum.inr (14, 56), Sum.inr (19, 5),
    Sum.inr (19, 58), Sum.inr (14, 7),
    Sum.inr (14, 4), Sum.inr (19, 57),
    Sum.inr (17, 13), Sum.inr (20, 48),
    Sum.inr (20, 51), Sum.inr (17, 14),
    Sum.inr (17, 1), Sum.inr (20, 60),
    Sum.inr (20, 63), Sum.inr (17, 2),
    Sum.inr (19, 54), Sum.inr (14, 11),
    Sum.inr (14, 8), Sum.inr (19, 53),
    Sum.inr (21, 37), Sum.inr (16, 24),
    Sum.inr (16, 27), Sum.inr (21, 38),
    Sum.inr (15, 18), Sum.inr (18, 47),
    Sum.inr (18, 44), Sum.inr (15, 17),
    Sum.inr (15, 30), Sum.inr (18, 35),
    Sum.inr (18, 32), Sum.inr (15, 29),
    Sum.inr (21, 41), Sum.inr (16, 20),
    Sum.inr (16, 23), Sum.inr (21, 42)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket21Sign : Fin 64 → ℤ :=
  ![1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1,
    1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1, 1, -1, -1, 1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket21Phase : Fin 64 → ZMod 2 :=
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
theorem generatedFifthXiShortPacket21_physical : ∀ e : Fin 64, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket21Source e)) i =
      2 * generatedFifthXiShortPacket21Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket21Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
