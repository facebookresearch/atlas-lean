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
def generatedFifthXiShortPacket03Target (e : Fin 64) : generatedFifthXiShortCachedLabel :=
  Sum.inr (3, e)

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket03Source : Fin 64 → generatedFifthXiShortCachedLabel :=
  ![Sum.inr (2, 61), Sum.inr (9, 0),
    Sum.inr (9, 3), Sum.inr (2, 62),
    Sum.inr (7, 10), Sum.inr (4, 55),
    Sum.inr (4, 52), Sum.inr (7, 9),
    Sum.inr (7, 6), Sum.inr (4, 59),
    Sum.inr (4, 56), Sum.inr (7, 5),
    Sum.inr (2, 49), Sum.inr (9, 12),
    Sum.inr (9, 15), Sum.inr (2, 50),
    Sum.inr (6, 34), Sum.inr (5, 31),
    Sum.inr (5, 28), Sum.inr (6, 33),
    Sum.inr (3, 21), Sum.inr (8, 40),
    Sum.inr (8, 43), Sum.inr (3, 22),
    Sum.inr (3, 25), Sum.inr (8, 36),
    Sum.inr (8, 39), Sum.inr (3, 26),
    Sum.inr (6, 46), Sum.inr (5, 19),
    Sum.inr (5, 16), Sum.inr (6, 45),
    Sum.inr (6, 18), Sum.inr (5, 47),
    Sum.inr (5, 44), Sum.inr (6, 17),
    Sum.inr (3, 37), Sum.inr (8, 24),
    Sum.inr (8, 27), Sum.inr (3, 38),
    Sum.inr (3, 41), Sum.inr (8, 20),
    Sum.inr (8, 23), Sum.inr (3, 42),
    Sum.inr (6, 30), Sum.inr (5, 35),
    Sum.inr (5, 32), Sum.inr (6, 29),
    Sum.inr (2, 13), Sum.inr (9, 48),
    Sum.inr (9, 51), Sum.inr (2, 14),
    Sum.inr (7, 58), Sum.inr (4, 7),
    Sum.inr (4, 4), Sum.inr (7, 57),
    Sum.inr (7, 54), Sum.inr (4, 11),
    Sum.inr (4, 8), Sum.inr (7, 53),
    Sum.inr (2, 1), Sum.inr (9, 60),
    Sum.inr (9, 63), Sum.inr (2, 2)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket03Sign : Fin 64 → ℤ :=
  ![1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1,
    1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1, 1, -1, -1, 1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket03Phase : Fin 64 → ZMod 2 :=
  ![1, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0,
    0, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0,
    1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 1,
    1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0,
    0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1,
    1, 1, 1, 0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Check 64 genuine source/target vectors in all 24 physical coordinates.
/-- Every displayed physical source has the asserted exact integer Xi image. -/
theorem generatedFifthXiShortPacket03_physical : ∀ e : Fin 64, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket03Source e)) i =
      2 * generatedFifthXiShortPacket03Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket03Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
