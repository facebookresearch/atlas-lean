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
def generatedFifthXiShortPacket52Target (e : Fin 64) : generatedFifthXiShortCachedLabel :=
  Sum.inr (52, e)

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket52Source : Fin 64 → generatedFifthXiShortCachedLabel :=
  ![Sum.inr (29, 0), Sum.inr (53, 61),
    Sum.inr (53, 62), Sum.inr (29, 3),
    Sum.inr (51, 55), Sum.inr (27, 10),
    Sum.inr (27, 9), Sum.inr (51, 52),
    Sum.inr (51, 59), Sum.inr (27, 6),
    Sum.inr (27, 5), Sum.inr (51, 56),
    Sum.inr (29, 12), Sum.inr (53, 49),
    Sum.inr (53, 50), Sum.inr (29, 15),
    Sum.inr (50, 31), Sum.inr (26, 34),
    Sum.inr (26, 33), Sum.inr (50, 28),
    Sum.inr (28, 40), Sum.inr (52, 21),
    Sum.inr (52, 22), Sum.inr (28, 43),
    Sum.inr (28, 36), Sum.inr (52, 25),
    Sum.inr (52, 26), Sum.inr (28, 39),
    Sum.inr (50, 19), Sum.inr (26, 46),
    Sum.inr (26, 45), Sum.inr (50, 16),
    Sum.inr (50, 47), Sum.inr (26, 18),
    Sum.inr (26, 17), Sum.inr (50, 44),
    Sum.inr (28, 24), Sum.inr (52, 37),
    Sum.inr (52, 38), Sum.inr (28, 27),
    Sum.inr (28, 20), Sum.inr (52, 41),
    Sum.inr (52, 42), Sum.inr (28, 23),
    Sum.inr (50, 35), Sum.inr (26, 30),
    Sum.inr (26, 29), Sum.inr (50, 32),
    Sum.inr (29, 48), Sum.inr (53, 13),
    Sum.inr (53, 14), Sum.inr (29, 51),
    Sum.inr (51, 7), Sum.inr (27, 58),
    Sum.inr (27, 57), Sum.inr (51, 4),
    Sum.inr (51, 11), Sum.inr (27, 54),
    Sum.inr (27, 53), Sum.inr (51, 8),
    Sum.inr (29, 60), Sum.inr (53, 1),
    Sum.inr (53, 2), Sum.inr (29, 63)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket52Sign : Fin 64 → ℤ :=
  ![-1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1,
    -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1, -1, 1, 1, -1, 1, -1, -1, 1,
    -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket52Phase : Fin 64 → ZMod 2 :=
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
theorem generatedFifthXiShortPacket52_physical : ∀ e : Fin 64, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket52Source e)) i =
      2 * generatedFifthXiShortPacket52Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket52Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
