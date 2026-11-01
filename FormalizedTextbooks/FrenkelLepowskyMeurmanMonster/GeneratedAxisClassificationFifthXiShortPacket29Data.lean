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
def generatedFifthXiShortPacket29Target (e : Fin 64) : generatedFifthXiShortCachedLabel :=
  Sum.inr (29, e)

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket29Source : Fin 64 → generatedFifthXiShortCachedLabel :=
  ![Sum.inr (29, 21), Sum.inr (53, 40),
    Sum.inr (53, 43), Sum.inr (29, 22),
    Sum.inr (51, 34), Sum.inr (27, 31),
    Sum.inr (27, 28), Sum.inr (51, 33),
    Sum.inr (51, 46), Sum.inr (27, 19),
    Sum.inr (27, 16), Sum.inr (51, 45),
    Sum.inr (29, 25), Sum.inr (53, 36),
    Sum.inr (53, 39), Sum.inr (29, 26),
    Sum.inr (50, 10), Sum.inr (26, 55),
    Sum.inr (26, 52), Sum.inr (50, 9),
    Sum.inr (28, 61), Sum.inr (52, 0),
    Sum.inr (52, 3), Sum.inr (28, 62),
    Sum.inr (28, 49), Sum.inr (52, 12),
    Sum.inr (52, 15), Sum.inr (28, 50),
    Sum.inr (50, 6), Sum.inr (26, 59),
    Sum.inr (26, 56), Sum.inr (50, 5),
    Sum.inr (50, 58), Sum.inr (26, 7),
    Sum.inr (26, 4), Sum.inr (50, 57),
    Sum.inr (28, 13), Sum.inr (52, 48),
    Sum.inr (52, 51), Sum.inr (28, 14),
    Sum.inr (28, 1), Sum.inr (52, 60),
    Sum.inr (52, 63), Sum.inr (28, 2),
    Sum.inr (50, 54), Sum.inr (26, 11),
    Sum.inr (26, 8), Sum.inr (50, 53),
    Sum.inr (29, 37), Sum.inr (53, 24),
    Sum.inr (53, 27), Sum.inr (29, 38),
    Sum.inr (51, 18), Sum.inr (27, 47),
    Sum.inr (27, 44), Sum.inr (51, 17),
    Sum.inr (51, 30), Sum.inr (27, 35),
    Sum.inr (27, 32), Sum.inr (51, 29),
    Sum.inr (29, 41), Sum.inr (53, 20),
    Sum.inr (53, 23), Sum.inr (29, 42)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket29Sign : Fin 64 → ℤ :=
  ![1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1,
    1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1, 1, -1, -1, 1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket29Phase : Fin 64 → ZMod 2 :=
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
theorem generatedFifthXiShortPacket29_physical : ∀ e : Fin 64, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket29Source e)) i =
      2 * generatedFifthXiShortPacket29Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket29Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
