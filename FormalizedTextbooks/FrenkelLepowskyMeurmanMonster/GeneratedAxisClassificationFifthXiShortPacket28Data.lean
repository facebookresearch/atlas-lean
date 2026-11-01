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
def generatedFifthXiShortPacket28Target (e : Fin 64) : generatedFifthXiShortCachedLabel :=
  Sum.inr (28, e)

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket28Source : Fin 64 → generatedFifthXiShortCachedLabel :=
  ![Sum.inr (29, 61), Sum.inr (53, 0),
    Sum.inr (53, 3), Sum.inr (29, 62),
    Sum.inr (51, 10), Sum.inr (27, 55),
    Sum.inr (27, 52), Sum.inr (51, 9),
    Sum.inr (51, 6), Sum.inr (27, 59),
    Sum.inr (27, 56), Sum.inr (51, 5),
    Sum.inr (29, 49), Sum.inr (53, 12),
    Sum.inr (53, 15), Sum.inr (29, 50),
    Sum.inr (50, 34), Sum.inr (26, 31),
    Sum.inr (26, 28), Sum.inr (50, 33),
    Sum.inr (28, 21), Sum.inr (52, 40),
    Sum.inr (52, 43), Sum.inr (28, 22),
    Sum.inr (28, 25), Sum.inr (52, 36),
    Sum.inr (52, 39), Sum.inr (28, 26),
    Sum.inr (50, 46), Sum.inr (26, 19),
    Sum.inr (26, 16), Sum.inr (50, 45),
    Sum.inr (50, 18), Sum.inr (26, 47),
    Sum.inr (26, 44), Sum.inr (50, 17),
    Sum.inr (28, 37), Sum.inr (52, 24),
    Sum.inr (52, 27), Sum.inr (28, 38),
    Sum.inr (28, 41), Sum.inr (52, 20),
    Sum.inr (52, 23), Sum.inr (28, 42),
    Sum.inr (50, 30), Sum.inr (26, 35),
    Sum.inr (26, 32), Sum.inr (50, 29),
    Sum.inr (29, 13), Sum.inr (53, 48),
    Sum.inr (53, 51), Sum.inr (29, 14),
    Sum.inr (51, 58), Sum.inr (27, 7),
    Sum.inr (27, 4), Sum.inr (51, 57),
    Sum.inr (51, 54), Sum.inr (27, 11),
    Sum.inr (27, 8), Sum.inr (51, 53),
    Sum.inr (29, 1), Sum.inr (53, 60),
    Sum.inr (53, 63), Sum.inr (29, 2)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket28Sign : Fin 64 → ℤ :=
  ![1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1,
    1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1, 1, -1, -1, 1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket28Phase : Fin 64 → ZMod 2 :=
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
theorem generatedFifthXiShortPacket28_physical : ∀ e : Fin 64, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket28Source e)) i =
      2 * generatedFifthXiShortPacket28Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket28Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
