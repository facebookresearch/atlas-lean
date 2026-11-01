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
def generatedFifthXiShortPacket51Target (e : Fin 64) : generatedFifthXiShortCachedLabel :=
  Sum.inr (51, e)

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket51Source : Fin 64 → generatedFifthXiShortCachedLabel :=
  ![Sum.inr (29, 34), Sum.inr (53, 31),
    Sum.inr (53, 28), Sum.inr (29, 33),
    Sum.inr (51, 21), Sum.inr (27, 40),
    Sum.inr (27, 43), Sum.inr (51, 22),
    Sum.inr (51, 25), Sum.inr (27, 36),
    Sum.inr (27, 39), Sum.inr (51, 26),
    Sum.inr (29, 46), Sum.inr (53, 19),
    Sum.inr (53, 16), Sum.inr (29, 45),
    Sum.inr (50, 61), Sum.inr (26, 0),
    Sum.inr (26, 3), Sum.inr (50, 62),
    Sum.inr (28, 10), Sum.inr (52, 55),
    Sum.inr (52, 52), Sum.inr (28, 9),
    Sum.inr (28, 6), Sum.inr (52, 59),
    Sum.inr (52, 56), Sum.inr (28, 5),
    Sum.inr (50, 49), Sum.inr (26, 12),
    Sum.inr (26, 15), Sum.inr (50, 50),
    Sum.inr (50, 13), Sum.inr (26, 48),
    Sum.inr (26, 51), Sum.inr (50, 14),
    Sum.inr (28, 58), Sum.inr (52, 7),
    Sum.inr (52, 4), Sum.inr (28, 57),
    Sum.inr (28, 54), Sum.inr (52, 11),
    Sum.inr (52, 8), Sum.inr (28, 53),
    Sum.inr (50, 1), Sum.inr (26, 60),
    Sum.inr (26, 63), Sum.inr (50, 2),
    Sum.inr (29, 18), Sum.inr (53, 47),
    Sum.inr (53, 44), Sum.inr (29, 17),
    Sum.inr (51, 37), Sum.inr (27, 24),
    Sum.inr (27, 27), Sum.inr (51, 38),
    Sum.inr (51, 41), Sum.inr (27, 20),
    Sum.inr (27, 23), Sum.inr (51, 42),
    Sum.inr (29, 30), Sum.inr (53, 35),
    Sum.inr (53, 32), Sum.inr (29, 29)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket51Sign : Fin 64 → ℤ :=
  ![-1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1,
    -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1, -1, 1, 1, -1, 1, -1, -1, 1,
    -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket51Phase : Fin 64 → ZMod 2 :=
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
theorem generatedFifthXiShortPacket51_physical : ∀ e : Fin 64, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket51Source e)) i =
      2 * generatedFifthXiShortPacket51Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket51Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
