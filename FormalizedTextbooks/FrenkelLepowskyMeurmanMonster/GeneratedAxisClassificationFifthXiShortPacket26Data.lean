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
def generatedFifthXiShortPacket26Target (e : Fin 64) : generatedFifthXiShortCachedLabel :=
  Sum.inr (26, e)

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket26Source : Fin 64 → generatedFifthXiShortCachedLabel :=
  ![Sum.inr (29, 55), Sum.inr (53, 10),
    Sum.inr (53, 9), Sum.inr (29, 52),
    Sum.inr (51, 0), Sum.inr (27, 61),
    Sum.inr (27, 62), Sum.inr (51, 3),
    Sum.inr (51, 12), Sum.inr (27, 49),
    Sum.inr (27, 50), Sum.inr (51, 15),
    Sum.inr (29, 59), Sum.inr (53, 6),
    Sum.inr (53, 5), Sum.inr (29, 56),
    Sum.inr (50, 40), Sum.inr (26, 21),
    Sum.inr (26, 22), Sum.inr (50, 43),
    Sum.inr (28, 31), Sum.inr (52, 34),
    Sum.inr (52, 33), Sum.inr (28, 28),
    Sum.inr (28, 19), Sum.inr (52, 46),
    Sum.inr (52, 45), Sum.inr (28, 16),
    Sum.inr (50, 36), Sum.inr (26, 25),
    Sum.inr (26, 26), Sum.inr (50, 39),
    Sum.inr (50, 24), Sum.inr (26, 37),
    Sum.inr (26, 38), Sum.inr (50, 27),
    Sum.inr (28, 47), Sum.inr (52, 18),
    Sum.inr (52, 17), Sum.inr (28, 44),
    Sum.inr (28, 35), Sum.inr (52, 30),
    Sum.inr (52, 29), Sum.inr (28, 32),
    Sum.inr (50, 20), Sum.inr (26, 41),
    Sum.inr (26, 42), Sum.inr (50, 23),
    Sum.inr (29, 7), Sum.inr (53, 58),
    Sum.inr (53, 57), Sum.inr (29, 4),
    Sum.inr (51, 48), Sum.inr (27, 13),
    Sum.inr (27, 14), Sum.inr (51, 51),
    Sum.inr (51, 60), Sum.inr (27, 1),
    Sum.inr (27, 2), Sum.inr (51, 63),
    Sum.inr (29, 11), Sum.inr (53, 54),
    Sum.inr (53, 53), Sum.inr (29, 8)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket26Sign : Fin 64 → ℤ :=
  ![1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1,
    1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1, 1, -1, -1, 1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket26Phase : Fin 64 → ZMod 2 :=
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
theorem generatedFifthXiShortPacket26_physical : ∀ e : Fin 64, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket26Source e)) i =
      2 * generatedFifthXiShortPacket26Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket26Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
