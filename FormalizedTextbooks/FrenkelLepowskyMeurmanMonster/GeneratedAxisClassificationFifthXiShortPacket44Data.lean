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
def generatedFifthXiShortPacket44Target (e : Fin 64) : generatedFifthXiShortCachedLabel :=
  Sum.inr (44, e)

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket44Source : Fin 64 → generatedFifthXiShortCachedLabel :=
  ![Sum.inr (37, 61), Sum.inr (34, 0),
    Sum.inr (34, 3), Sum.inr (37, 62),
    Sum.inr (36, 10), Sum.inr (35, 55),
    Sum.inr (35, 52), Sum.inr (36, 9),
    Sum.inr (36, 6), Sum.inr (35, 59),
    Sum.inr (35, 56), Sum.inr (36, 5),
    Sum.inr (37, 49), Sum.inr (34, 12),
    Sum.inr (34, 15), Sum.inr (37, 50),
    Sum.inr (45, 34), Sum.inr (42, 31),
    Sum.inr (42, 28), Sum.inr (45, 33),
    Sum.inr (44, 21), Sum.inr (43, 40),
    Sum.inr (43, 43), Sum.inr (44, 22),
    Sum.inr (44, 25), Sum.inr (43, 36),
    Sum.inr (43, 39), Sum.inr (44, 26),
    Sum.inr (45, 46), Sum.inr (42, 19),
    Sum.inr (42, 16), Sum.inr (45, 45),
    Sum.inr (45, 18), Sum.inr (42, 47),
    Sum.inr (42, 44), Sum.inr (45, 17),
    Sum.inr (44, 37), Sum.inr (43, 24),
    Sum.inr (43, 27), Sum.inr (44, 38),
    Sum.inr (44, 41), Sum.inr (43, 20),
    Sum.inr (43, 23), Sum.inr (44, 42),
    Sum.inr (45, 30), Sum.inr (42, 35),
    Sum.inr (42, 32), Sum.inr (45, 29),
    Sum.inr (37, 13), Sum.inr (34, 48),
    Sum.inr (34, 51), Sum.inr (37, 14),
    Sum.inr (36, 58), Sum.inr (35, 7),
    Sum.inr (35, 4), Sum.inr (36, 57),
    Sum.inr (36, 54), Sum.inr (35, 11),
    Sum.inr (35, 8), Sum.inr (36, 53),
    Sum.inr (37, 1), Sum.inr (34, 60),
    Sum.inr (34, 63), Sum.inr (37, 2)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket44Sign : Fin 64 → ℤ :=
  ![1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1,
    1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1, 1, -1, -1, 1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket44Phase : Fin 64 → ZMod 2 :=
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
theorem generatedFifthXiShortPacket44_physical : ∀ e : Fin 64, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket44Source e)) i =
      2 * generatedFifthXiShortPacket44Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket44Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
