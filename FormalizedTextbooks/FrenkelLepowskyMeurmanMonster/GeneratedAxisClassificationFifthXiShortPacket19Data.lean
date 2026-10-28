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
def generatedFifthXiShortPacket19Target (e : Fin 64) : generatedFifthXiShortCachedLabel :=
  Sum.inr (19, e)

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket19Source : Fin 64 → generatedFifthXiShortCachedLabel :=
  ![Sum.inr (21, 10), Sum.inr (16, 55),
    Sum.inr (16, 52), Sum.inr (21, 9),
    Sum.inr (15, 61), Sum.inr (18, 0),
    Sum.inr (18, 3), Sum.inr (15, 62),
    Sum.inr (15, 49), Sum.inr (18, 12),
    Sum.inr (18, 15), Sum.inr (15, 50),
    Sum.inr (21, 6), Sum.inr (16, 59),
    Sum.inr (16, 56), Sum.inr (21, 5),
    Sum.inr (19, 21), Sum.inr (14, 40),
    Sum.inr (14, 43), Sum.inr (19, 22),
    Sum.inr (17, 34), Sum.inr (20, 31),
    Sum.inr (20, 28), Sum.inr (17, 33),
    Sum.inr (17, 46), Sum.inr (20, 19),
    Sum.inr (20, 16), Sum.inr (17, 45),
    Sum.inr (19, 25), Sum.inr (14, 36),
    Sum.inr (14, 39), Sum.inr (19, 26),
    Sum.inr (19, 37), Sum.inr (14, 24),
    Sum.inr (14, 27), Sum.inr (19, 38),
    Sum.inr (17, 18), Sum.inr (20, 47),
    Sum.inr (20, 44), Sum.inr (17, 17),
    Sum.inr (17, 30), Sum.inr (20, 35),
    Sum.inr (20, 32), Sum.inr (17, 29),
    Sum.inr (19, 41), Sum.inr (14, 20),
    Sum.inr (14, 23), Sum.inr (19, 42),
    Sum.inr (21, 58), Sum.inr (16, 7),
    Sum.inr (16, 4), Sum.inr (21, 57),
    Sum.inr (15, 13), Sum.inr (18, 48),
    Sum.inr (18, 51), Sum.inr (15, 14),
    Sum.inr (15, 1), Sum.inr (18, 60),
    Sum.inr (18, 63), Sum.inr (15, 2),
    Sum.inr (21, 54), Sum.inr (16, 11),
    Sum.inr (16, 8), Sum.inr (21, 53)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket19Sign : Fin 64 → ℤ :=
  ![-1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1,
    -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1, -1, 1, 1, -1, 1, -1, -1, 1,
    -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket19Phase : Fin 64 → ZMod 2 :=
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
theorem generatedFifthXiShortPacket19_physical : ∀ e : Fin 64, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket19Source e)) i =
      2 * generatedFifthXiShortPacket19Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket19Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
