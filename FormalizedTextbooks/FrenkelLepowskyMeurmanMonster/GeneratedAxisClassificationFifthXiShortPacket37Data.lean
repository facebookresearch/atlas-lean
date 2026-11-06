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
def generatedFifthXiShortPacket37Target (e : Fin 64) : generatedFifthXiShortCachedLabel :=
  Sum.inr (37, e)

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket37Source : Fin 64 → generatedFifthXiShortCachedLabel :=
  ![Sum.inr (37, 21), Sum.inr (34, 40),
    Sum.inr (34, 43), Sum.inr (37, 22),
    Sum.inr (36, 34), Sum.inr (35, 31),
    Sum.inr (35, 28), Sum.inr (36, 33),
    Sum.inr (36, 46), Sum.inr (35, 19),
    Sum.inr (35, 16), Sum.inr (36, 45),
    Sum.inr (37, 25), Sum.inr (34, 36),
    Sum.inr (34, 39), Sum.inr (37, 26),
    Sum.inr (45, 10), Sum.inr (42, 55),
    Sum.inr (42, 52), Sum.inr (45, 9),
    Sum.inr (44, 61), Sum.inr (43, 0),
    Sum.inr (43, 3), Sum.inr (44, 62),
    Sum.inr (44, 49), Sum.inr (43, 12),
    Sum.inr (43, 15), Sum.inr (44, 50),
    Sum.inr (45, 6), Sum.inr (42, 59),
    Sum.inr (42, 56), Sum.inr (45, 5),
    Sum.inr (45, 58), Sum.inr (42, 7),
    Sum.inr (42, 4), Sum.inr (45, 57),
    Sum.inr (44, 13), Sum.inr (43, 48),
    Sum.inr (43, 51), Sum.inr (44, 14),
    Sum.inr (44, 1), Sum.inr (43, 60),
    Sum.inr (43, 63), Sum.inr (44, 2),
    Sum.inr (45, 54), Sum.inr (42, 11),
    Sum.inr (42, 8), Sum.inr (45, 53),
    Sum.inr (37, 37), Sum.inr (34, 24),
    Sum.inr (34, 27), Sum.inr (37, 38),
    Sum.inr (36, 18), Sum.inr (35, 47),
    Sum.inr (35, 44), Sum.inr (36, 17),
    Sum.inr (36, 30), Sum.inr (35, 35),
    Sum.inr (35, 32), Sum.inr (36, 29),
    Sum.inr (37, 41), Sum.inr (34, 20),
    Sum.inr (34, 23), Sum.inr (37, 42)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket37Sign : Fin 64 → ℤ :=
  ![1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1,
    1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1, 1, -1, -1, 1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket37Phase : Fin 64 → ZMod 2 :=
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
theorem generatedFifthXiShortPacket37_physical : ∀ e : Fin 64, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket37Source e)) i =
      2 * generatedFifthXiShortPacket37Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket37Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
