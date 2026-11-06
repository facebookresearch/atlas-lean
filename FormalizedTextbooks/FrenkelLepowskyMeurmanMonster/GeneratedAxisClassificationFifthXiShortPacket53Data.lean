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
def generatedFifthXiShortPacket53Target (e : Fin 64) : generatedFifthXiShortCachedLabel :=
  Sum.inr (53, e)

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket53Source : Fin 64 → generatedFifthXiShortCachedLabel :=
  ![Sum.inr (29, 40), Sum.inr (53, 21),
    Sum.inr (53, 22), Sum.inr (29, 43),
    Sum.inr (51, 31), Sum.inr (27, 34),
    Sum.inr (27, 33), Sum.inr (51, 28),
    Sum.inr (51, 19), Sum.inr (27, 46),
    Sum.inr (27, 45), Sum.inr (51, 16),
    Sum.inr (29, 36), Sum.inr (53, 25),
    Sum.inr (53, 26), Sum.inr (29, 39),
    Sum.inr (50, 55), Sum.inr (26, 10),
    Sum.inr (26, 9), Sum.inr (50, 52),
    Sum.inr (28, 0), Sum.inr (52, 61),
    Sum.inr (52, 62), Sum.inr (28, 3),
    Sum.inr (28, 12), Sum.inr (52, 49),
    Sum.inr (52, 50), Sum.inr (28, 15),
    Sum.inr (50, 59), Sum.inr (26, 6),
    Sum.inr (26, 5), Sum.inr (50, 56),
    Sum.inr (50, 7), Sum.inr (26, 58),
    Sum.inr (26, 57), Sum.inr (50, 4),
    Sum.inr (28, 48), Sum.inr (52, 13),
    Sum.inr (52, 14), Sum.inr (28, 51),
    Sum.inr (28, 60), Sum.inr (52, 1),
    Sum.inr (52, 2), Sum.inr (28, 63),
    Sum.inr (50, 11), Sum.inr (26, 54),
    Sum.inr (26, 53), Sum.inr (50, 8),
    Sum.inr (29, 24), Sum.inr (53, 37),
    Sum.inr (53, 38), Sum.inr (29, 27),
    Sum.inr (51, 47), Sum.inr (27, 18),
    Sum.inr (27, 17), Sum.inr (51, 44),
    Sum.inr (51, 35), Sum.inr (27, 30),
    Sum.inr (27, 29), Sum.inr (51, 32),
    Sum.inr (29, 20), Sum.inr (53, 41),
    Sum.inr (53, 42), Sum.inr (29, 23)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket53Sign : Fin 64 → ℤ :=
  ![-1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1,
    -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1, -1, 1, 1, -1, 1, -1, -1, 1,
    -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket53Phase : Fin 64 → ZMod 2 :=
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
theorem generatedFifthXiShortPacket53_physical : ∀ e : Fin 64, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket53Source e)) i =
      2 * generatedFifthXiShortPacket53Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket53Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
