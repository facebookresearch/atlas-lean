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
def generatedFifthXiShortPacket36Target (e : Fin 64) : generatedFifthXiShortCachedLabel :=
  Sum.inr (36, e)

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket36Source : Fin 64 → generatedFifthXiShortCachedLabel :=
  ![Sum.inr (37, 34), Sum.inr (34, 31),
    Sum.inr (34, 28), Sum.inr (37, 33),
    Sum.inr (36, 21), Sum.inr (35, 40),
    Sum.inr (35, 43), Sum.inr (36, 22),
    Sum.inr (36, 25), Sum.inr (35, 36),
    Sum.inr (35, 39), Sum.inr (36, 26),
    Sum.inr (37, 46), Sum.inr (34, 19),
    Sum.inr (34, 16), Sum.inr (37, 45),
    Sum.inr (45, 61), Sum.inr (42, 0),
    Sum.inr (42, 3), Sum.inr (45, 62),
    Sum.inr (44, 10), Sum.inr (43, 55),
    Sum.inr (43, 52), Sum.inr (44, 9),
    Sum.inr (44, 6), Sum.inr (43, 59),
    Sum.inr (43, 56), Sum.inr (44, 5),
    Sum.inr (45, 49), Sum.inr (42, 12),
    Sum.inr (42, 15), Sum.inr (45, 50),
    Sum.inr (45, 13), Sum.inr (42, 48),
    Sum.inr (42, 51), Sum.inr (45, 14),
    Sum.inr (44, 58), Sum.inr (43, 7),
    Sum.inr (43, 4), Sum.inr (44, 57),
    Sum.inr (44, 54), Sum.inr (43, 11),
    Sum.inr (43, 8), Sum.inr (44, 53),
    Sum.inr (45, 1), Sum.inr (42, 60),
    Sum.inr (42, 63), Sum.inr (45, 2),
    Sum.inr (37, 18), Sum.inr (34, 47),
    Sum.inr (34, 44), Sum.inr (37, 17),
    Sum.inr (36, 37), Sum.inr (35, 24),
    Sum.inr (35, 27), Sum.inr (36, 38),
    Sum.inr (36, 41), Sum.inr (35, 20),
    Sum.inr (35, 23), Sum.inr (36, 42),
    Sum.inr (37, 30), Sum.inr (34, 35),
    Sum.inr (34, 32), Sum.inr (37, 29)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket36Sign : Fin 64 → ℤ :=
  ![-1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1,
    -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1, -1, 1, 1, -1, 1, -1, -1, 1,
    -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket36Phase : Fin 64 → ZMod 2 :=
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
theorem generatedFifthXiShortPacket36_physical : ∀ e : Fin 64, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket36Source e)) i =
      2 * generatedFifthXiShortPacket36Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket36Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
