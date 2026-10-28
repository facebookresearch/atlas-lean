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
def generatedFifthXiShortPacket06Target (e : Fin 64) : generatedFifthXiShortCachedLabel :=
  Sum.inr (6, e)

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket06Source : Fin 64 → generatedFifthXiShortCachedLabel :=
  ![Sum.inr (2, 10), Sum.inr (9, 55),
    Sum.inr (9, 52), Sum.inr (2, 9),
    Sum.inr (7, 61), Sum.inr (4, 0),
    Sum.inr (4, 3), Sum.inr (7, 62),
    Sum.inr (7, 49), Sum.inr (4, 12),
    Sum.inr (4, 15), Sum.inr (7, 50),
    Sum.inr (2, 6), Sum.inr (9, 59),
    Sum.inr (9, 56), Sum.inr (2, 5),
    Sum.inr (6, 21), Sum.inr (5, 40),
    Sum.inr (5, 43), Sum.inr (6, 22),
    Sum.inr (3, 34), Sum.inr (8, 31),
    Sum.inr (8, 28), Sum.inr (3, 33),
    Sum.inr (3, 46), Sum.inr (8, 19),
    Sum.inr (8, 16), Sum.inr (3, 45),
    Sum.inr (6, 25), Sum.inr (5, 36),
    Sum.inr (5, 39), Sum.inr (6, 26),
    Sum.inr (6, 37), Sum.inr (5, 24),
    Sum.inr (5, 27), Sum.inr (6, 38),
    Sum.inr (3, 18), Sum.inr (8, 47),
    Sum.inr (8, 44), Sum.inr (3, 17),
    Sum.inr (3, 30), Sum.inr (8, 35),
    Sum.inr (8, 32), Sum.inr (3, 29),
    Sum.inr (6, 41), Sum.inr (5, 20),
    Sum.inr (5, 23), Sum.inr (6, 42),
    Sum.inr (2, 58), Sum.inr (9, 7),
    Sum.inr (9, 4), Sum.inr (2, 57),
    Sum.inr (7, 13), Sum.inr (4, 48),
    Sum.inr (4, 51), Sum.inr (7, 14),
    Sum.inr (7, 1), Sum.inr (4, 60),
    Sum.inr (4, 63), Sum.inr (7, 2),
    Sum.inr (2, 54), Sum.inr (9, 11),
    Sum.inr (9, 8), Sum.inr (2, 53)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket06Sign : Fin 64 → ℤ :=
  ![-1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1,
    -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1, -1, 1, 1, -1, 1, -1, -1, 1,
    -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket06Phase : Fin 64 → ZMod 2 :=
  ![0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1,
    1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0,
    1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1,
    1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0,
    1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 0,
    0, 1, 1, 1]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Check 64 genuine source/target vectors in all 24 physical coordinates.
/-- Every displayed physical source has the asserted exact integer Xi image. -/
theorem generatedFifthXiShortPacket06_physical : ∀ e : Fin 64, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket06Source e)) i =
      2 * generatedFifthXiShortPacket06Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket06Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
