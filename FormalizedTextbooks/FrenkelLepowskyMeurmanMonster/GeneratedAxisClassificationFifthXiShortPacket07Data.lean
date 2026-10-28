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
def generatedFifthXiShortPacket07Target (e : Fin 64) : generatedFifthXiShortCachedLabel :=
  Sum.inr (7, e)

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket07Source : Fin 64 → generatedFifthXiShortCachedLabel :=
  ![Sum.inr (2, 34), Sum.inr (9, 31),
    Sum.inr (9, 28), Sum.inr (2, 33),
    Sum.inr (7, 21), Sum.inr (4, 40),
    Sum.inr (4, 43), Sum.inr (7, 22),
    Sum.inr (7, 25), Sum.inr (4, 36),
    Sum.inr (4, 39), Sum.inr (7, 26),
    Sum.inr (2, 46), Sum.inr (9, 19),
    Sum.inr (9, 16), Sum.inr (2, 45),
    Sum.inr (6, 61), Sum.inr (5, 0),
    Sum.inr (5, 3), Sum.inr (6, 62),
    Sum.inr (3, 10), Sum.inr (8, 55),
    Sum.inr (8, 52), Sum.inr (3, 9),
    Sum.inr (3, 6), Sum.inr (8, 59),
    Sum.inr (8, 56), Sum.inr (3, 5),
    Sum.inr (6, 49), Sum.inr (5, 12),
    Sum.inr (5, 15), Sum.inr (6, 50),
    Sum.inr (6, 13), Sum.inr (5, 48),
    Sum.inr (5, 51), Sum.inr (6, 14),
    Sum.inr (3, 58), Sum.inr (8, 7),
    Sum.inr (8, 4), Sum.inr (3, 57),
    Sum.inr (3, 54), Sum.inr (8, 11),
    Sum.inr (8, 8), Sum.inr (3, 53),
    Sum.inr (6, 1), Sum.inr (5, 60),
    Sum.inr (5, 63), Sum.inr (6, 2),
    Sum.inr (2, 18), Sum.inr (9, 47),
    Sum.inr (9, 44), Sum.inr (2, 17),
    Sum.inr (7, 37), Sum.inr (4, 24),
    Sum.inr (4, 27), Sum.inr (7, 38),
    Sum.inr (7, 41), Sum.inr (4, 20),
    Sum.inr (4, 23), Sum.inr (7, 42),
    Sum.inr (2, 30), Sum.inr (9, 35),
    Sum.inr (9, 32), Sum.inr (2, 29)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket07Sign : Fin 64 → ℤ :=
  ![-1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1,
    -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1, -1, 1, 1, -1, 1, -1, -1, 1,
    -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket07Phase : Fin 64 → ZMod 2 :=
  ![0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0,
    1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0,
    1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0,
    1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1,
    1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1,
    0, 1, 1, 1]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Check 64 genuine source/target vectors in all 24 physical coordinates.
/-- Every displayed physical source has the asserted exact integer Xi image. -/
theorem generatedFifthXiShortPacket07_physical : ∀ e : Fin 64, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket07Source e)) i =
      2 * generatedFifthXiShortPacket07Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket07Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
