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
def generatedFifthXiShortPacket02Target (e : Fin 64) : generatedFifthXiShortCachedLabel :=
  Sum.inr (2, e)

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket02Source : Fin 64 → generatedFifthXiShortCachedLabel :=
  ![Sum.inr (2, 21), Sum.inr (9, 40),
    Sum.inr (9, 43), Sum.inr (2, 22),
    Sum.inr (7, 34), Sum.inr (4, 31),
    Sum.inr (4, 28), Sum.inr (7, 33),
    Sum.inr (7, 46), Sum.inr (4, 19),
    Sum.inr (4, 16), Sum.inr (7, 45),
    Sum.inr (2, 25), Sum.inr (9, 36),
    Sum.inr (9, 39), Sum.inr (2, 26),
    Sum.inr (6, 10), Sum.inr (5, 55),
    Sum.inr (5, 52), Sum.inr (6, 9),
    Sum.inr (3, 61), Sum.inr (8, 0),
    Sum.inr (8, 3), Sum.inr (3, 62),
    Sum.inr (3, 49), Sum.inr (8, 12),
    Sum.inr (8, 15), Sum.inr (3, 50),
    Sum.inr (6, 6), Sum.inr (5, 59),
    Sum.inr (5, 56), Sum.inr (6, 5),
    Sum.inr (6, 58), Sum.inr (5, 7),
    Sum.inr (5, 4), Sum.inr (6, 57),
    Sum.inr (3, 13), Sum.inr (8, 48),
    Sum.inr (8, 51), Sum.inr (3, 14),
    Sum.inr (3, 1), Sum.inr (8, 60),
    Sum.inr (8, 63), Sum.inr (3, 2),
    Sum.inr (6, 54), Sum.inr (5, 11),
    Sum.inr (5, 8), Sum.inr (6, 53),
    Sum.inr (2, 37), Sum.inr (9, 24),
    Sum.inr (9, 27), Sum.inr (2, 38),
    Sum.inr (7, 18), Sum.inr (4, 47),
    Sum.inr (4, 44), Sum.inr (7, 17),
    Sum.inr (7, 30), Sum.inr (4, 35),
    Sum.inr (4, 32), Sum.inr (7, 29),
    Sum.inr (2, 41), Sum.inr (9, 20),
    Sum.inr (9, 23), Sum.inr (2, 42)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket02Sign : Fin 64 → ℤ :=
  ![1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1,
    1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1, 1, -1, -1, 1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket02Phase : Fin 64 → ZMod 2 :=
  ![0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0,
    1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 0, 1,
    0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1,
    0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0,
    1, 1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 1,
    0, 0, 0, 1]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Check 64 genuine source/target vectors in all 24 physical coordinates.
/-- Every displayed physical source has the asserted exact integer Xi image. -/
theorem generatedFifthXiShortPacket02_physical : ∀ e : Fin 64, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket02Source e)) i =
      2 * generatedFifthXiShortPacket02Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket02Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
