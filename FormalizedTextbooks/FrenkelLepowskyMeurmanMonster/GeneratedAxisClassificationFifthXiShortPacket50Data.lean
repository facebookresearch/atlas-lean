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
def generatedFifthXiShortPacket50Target (e : Fin 64) : generatedFifthXiShortCachedLabel :=
  Sum.inr (50, e)

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket50Source : Fin 64 → generatedFifthXiShortCachedLabel :=
  ![Sum.inr (29, 10), Sum.inr (53, 55),
    Sum.inr (53, 52), Sum.inr (29, 9),
    Sum.inr (51, 61), Sum.inr (27, 0),
    Sum.inr (27, 3), Sum.inr (51, 62),
    Sum.inr (51, 49), Sum.inr (27, 12),
    Sum.inr (27, 15), Sum.inr (51, 50),
    Sum.inr (29, 6), Sum.inr (53, 59),
    Sum.inr (53, 56), Sum.inr (29, 5),
    Sum.inr (50, 21), Sum.inr (26, 40),
    Sum.inr (26, 43), Sum.inr (50, 22),
    Sum.inr (28, 34), Sum.inr (52, 31),
    Sum.inr (52, 28), Sum.inr (28, 33),
    Sum.inr (28, 46), Sum.inr (52, 19),
    Sum.inr (52, 16), Sum.inr (28, 45),
    Sum.inr (50, 25), Sum.inr (26, 36),
    Sum.inr (26, 39), Sum.inr (50, 26),
    Sum.inr (50, 37), Sum.inr (26, 24),
    Sum.inr (26, 27), Sum.inr (50, 38),
    Sum.inr (28, 18), Sum.inr (52, 47),
    Sum.inr (52, 44), Sum.inr (28, 17),
    Sum.inr (28, 30), Sum.inr (52, 35),
    Sum.inr (52, 32), Sum.inr (28, 29),
    Sum.inr (50, 41), Sum.inr (26, 20),
    Sum.inr (26, 23), Sum.inr (50, 42),
    Sum.inr (29, 58), Sum.inr (53, 7),
    Sum.inr (53, 4), Sum.inr (29, 57),
    Sum.inr (51, 13), Sum.inr (27, 48),
    Sum.inr (27, 51), Sum.inr (51, 14),
    Sum.inr (51, 1), Sum.inr (27, 60),
    Sum.inr (27, 63), Sum.inr (51, 2),
    Sum.inr (29, 54), Sum.inr (53, 11),
    Sum.inr (53, 8), Sum.inr (29, 53)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket50Sign : Fin 64 → ℤ :=
  ![-1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1,
    -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1, -1, 1, 1, -1, 1, -1, -1, 1,
    -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket50Phase : Fin 64 → ZMod 2 :=
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
theorem generatedFifthXiShortPacket50_physical : ∀ e : Fin 64, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket50Source e)) i =
      2 * generatedFifthXiShortPacket50Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket50Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
