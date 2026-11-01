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
def generatedFifthXiShortPacket45Target (e : Fin 64) : generatedFifthXiShortCachedLabel :=
  Sum.inr (45, e)

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket45Source : Fin 64 → generatedFifthXiShortCachedLabel :=
  ![Sum.inr (37, 10), Sum.inr (34, 55),
    Sum.inr (34, 52), Sum.inr (37, 9),
    Sum.inr (36, 61), Sum.inr (35, 0),
    Sum.inr (35, 3), Sum.inr (36, 62),
    Sum.inr (36, 49), Sum.inr (35, 12),
    Sum.inr (35, 15), Sum.inr (36, 50),
    Sum.inr (37, 6), Sum.inr (34, 59),
    Sum.inr (34, 56), Sum.inr (37, 5),
    Sum.inr (45, 21), Sum.inr (42, 40),
    Sum.inr (42, 43), Sum.inr (45, 22),
    Sum.inr (44, 34), Sum.inr (43, 31),
    Sum.inr (43, 28), Sum.inr (44, 33),
    Sum.inr (44, 46), Sum.inr (43, 19),
    Sum.inr (43, 16), Sum.inr (44, 45),
    Sum.inr (45, 25), Sum.inr (42, 36),
    Sum.inr (42, 39), Sum.inr (45, 26),
    Sum.inr (45, 37), Sum.inr (42, 24),
    Sum.inr (42, 27), Sum.inr (45, 38),
    Sum.inr (44, 18), Sum.inr (43, 47),
    Sum.inr (43, 44), Sum.inr (44, 17),
    Sum.inr (44, 30), Sum.inr (43, 35),
    Sum.inr (43, 32), Sum.inr (44, 29),
    Sum.inr (45, 41), Sum.inr (42, 20),
    Sum.inr (42, 23), Sum.inr (45, 42),
    Sum.inr (37, 58), Sum.inr (34, 7),
    Sum.inr (34, 4), Sum.inr (37, 57),
    Sum.inr (36, 13), Sum.inr (35, 48),
    Sum.inr (35, 51), Sum.inr (36, 14),
    Sum.inr (36, 1), Sum.inr (35, 60),
    Sum.inr (35, 63), Sum.inr (36, 2),
    Sum.inr (37, 54), Sum.inr (34, 11),
    Sum.inr (34, 8), Sum.inr (37, 53)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket45Sign : Fin 64 → ℤ :=
  ![-1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1,
    -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1, -1, 1, 1, -1, 1, -1, -1, 1,
    -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket45Phase : Fin 64 → ZMod 2 :=
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
theorem generatedFifthXiShortPacket45_physical : ∀ e : Fin 64, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket45Source e)) i =
      2 * generatedFifthXiShortPacket45Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket45Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
