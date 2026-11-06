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
def generatedFifthXiShortPacket27Target (e : Fin 64) : generatedFifthXiShortCachedLabel :=
  Sum.inr (27, e)

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket27Source : Fin 64 → generatedFifthXiShortCachedLabel :=
  ![Sum.inr (29, 31), Sum.inr (53, 34),
    Sum.inr (53, 33), Sum.inr (29, 28),
    Sum.inr (51, 40), Sum.inr (27, 21),
    Sum.inr (27, 22), Sum.inr (51, 43),
    Sum.inr (51, 36), Sum.inr (27, 25),
    Sum.inr (27, 26), Sum.inr (51, 39),
    Sum.inr (29, 19), Sum.inr (53, 46),
    Sum.inr (53, 45), Sum.inr (29, 16),
    Sum.inr (50, 0), Sum.inr (26, 61),
    Sum.inr (26, 62), Sum.inr (50, 3),
    Sum.inr (28, 55), Sum.inr (52, 10),
    Sum.inr (52, 9), Sum.inr (28, 52),
    Sum.inr (28, 59), Sum.inr (52, 6),
    Sum.inr (52, 5), Sum.inr (28, 56),
    Sum.inr (50, 12), Sum.inr (26, 49),
    Sum.inr (26, 50), Sum.inr (50, 15),
    Sum.inr (50, 48), Sum.inr (26, 13),
    Sum.inr (26, 14), Sum.inr (50, 51),
    Sum.inr (28, 7), Sum.inr (52, 58),
    Sum.inr (52, 57), Sum.inr (28, 4),
    Sum.inr (28, 11), Sum.inr (52, 54),
    Sum.inr (52, 53), Sum.inr (28, 8),
    Sum.inr (50, 60), Sum.inr (26, 1),
    Sum.inr (26, 2), Sum.inr (50, 63),
    Sum.inr (29, 47), Sum.inr (53, 18),
    Sum.inr (53, 17), Sum.inr (29, 44),
    Sum.inr (51, 24), Sum.inr (27, 37),
    Sum.inr (27, 38), Sum.inr (51, 27),
    Sum.inr (51, 20), Sum.inr (27, 41),
    Sum.inr (27, 42), Sum.inr (51, 23),
    Sum.inr (29, 35), Sum.inr (53, 30),
    Sum.inr (53, 29), Sum.inr (29, 32)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket27Sign : Fin 64 → ℤ :=
  ![1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1,
    1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1, 1, -1, -1, 1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket27Phase : Fin 64 → ZMod 2 :=
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
theorem generatedFifthXiShortPacket27_physical : ∀ e : Fin 64, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket27Source e)) i =
      2 * generatedFifthXiShortPacket27Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket27Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
