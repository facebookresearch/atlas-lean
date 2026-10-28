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
def generatedFifthXiShortPacket33Target (e : Fin 64) : generatedFifthXiShortCachedLabel :=
  Sum.inr (33, e)

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket33Source : Fin 64 → generatedFifthXiShortCachedLabel :=
  ![Sum.inr (32, 34), Sum.inr (39, 31),
    Sum.inr (39, 28), Sum.inr (32, 33),
    Sum.inr (33, 21), Sum.inr (38, 40),
    Sum.inr (38, 43), Sum.inr (33, 22),
    Sum.inr (33, 25), Sum.inr (38, 36),
    Sum.inr (38, 39), Sum.inr (33, 26),
    Sum.inr (32, 46), Sum.inr (39, 19),
    Sum.inr (39, 16), Sum.inr (32, 45),
    Sum.inr (40, 61), Sum.inr (47, 0),
    Sum.inr (47, 3), Sum.inr (40, 62),
    Sum.inr (41, 10), Sum.inr (46, 55),
    Sum.inr (46, 52), Sum.inr (41, 9),
    Sum.inr (41, 6), Sum.inr (46, 59),
    Sum.inr (46, 56), Sum.inr (41, 5),
    Sum.inr (40, 49), Sum.inr (47, 12),
    Sum.inr (47, 15), Sum.inr (40, 50),
    Sum.inr (40, 13), Sum.inr (47, 48),
    Sum.inr (47, 51), Sum.inr (40, 14),
    Sum.inr (41, 58), Sum.inr (46, 7),
    Sum.inr (46, 4), Sum.inr (41, 57),
    Sum.inr (41, 54), Sum.inr (46, 11),
    Sum.inr (46, 8), Sum.inr (41, 53),
    Sum.inr (40, 1), Sum.inr (47, 60),
    Sum.inr (47, 63), Sum.inr (40, 2),
    Sum.inr (32, 18), Sum.inr (39, 47),
    Sum.inr (39, 44), Sum.inr (32, 17),
    Sum.inr (33, 37), Sum.inr (38, 24),
    Sum.inr (38, 27), Sum.inr (33, 38),
    Sum.inr (33, 41), Sum.inr (38, 20),
    Sum.inr (38, 23), Sum.inr (33, 42),
    Sum.inr (32, 30), Sum.inr (39, 35),
    Sum.inr (39, 32), Sum.inr (32, 29)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket33Sign : Fin 64 → ℤ :=
  ![-1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1,
    -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1, -1, 1, 1, -1, 1, -1, -1, 1,
    -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket33Phase : Fin 64 → ZMod 2 :=
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
theorem generatedFifthXiShortPacket33_physical : ∀ e : Fin 64, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket33Source e)) i =
      2 * generatedFifthXiShortPacket33Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket33Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
