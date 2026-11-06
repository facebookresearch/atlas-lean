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
def generatedFifthXiShortPacket43Target (e : Fin 64) : generatedFifthXiShortCachedLabel :=
  Sum.inr (43, e)

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket43Source : Fin 64 → generatedFifthXiShortCachedLabel :=
  ![Sum.inr (37, 0), Sum.inr (34, 61),
    Sum.inr (34, 62), Sum.inr (37, 3),
    Sum.inr (36, 55), Sum.inr (35, 10),
    Sum.inr (35, 9), Sum.inr (36, 52),
    Sum.inr (36, 59), Sum.inr (35, 6),
    Sum.inr (35, 5), Sum.inr (36, 56),
    Sum.inr (37, 12), Sum.inr (34, 49),
    Sum.inr (34, 50), Sum.inr (37, 15),
    Sum.inr (45, 31), Sum.inr (42, 34),
    Sum.inr (42, 33), Sum.inr (45, 28),
    Sum.inr (44, 40), Sum.inr (43, 21),
    Sum.inr (43, 22), Sum.inr (44, 43),
    Sum.inr (44, 36), Sum.inr (43, 25),
    Sum.inr (43, 26), Sum.inr (44, 39),
    Sum.inr (45, 19), Sum.inr (42, 46),
    Sum.inr (42, 45), Sum.inr (45, 16),
    Sum.inr (45, 47), Sum.inr (42, 18),
    Sum.inr (42, 17), Sum.inr (45, 44),
    Sum.inr (44, 24), Sum.inr (43, 37),
    Sum.inr (43, 38), Sum.inr (44, 27),
    Sum.inr (44, 20), Sum.inr (43, 41),
    Sum.inr (43, 42), Sum.inr (44, 23),
    Sum.inr (45, 35), Sum.inr (42, 30),
    Sum.inr (42, 29), Sum.inr (45, 32),
    Sum.inr (37, 48), Sum.inr (34, 13),
    Sum.inr (34, 14), Sum.inr (37, 51),
    Sum.inr (36, 7), Sum.inr (35, 58),
    Sum.inr (35, 57), Sum.inr (36, 4),
    Sum.inr (36, 11), Sum.inr (35, 54),
    Sum.inr (35, 53), Sum.inr (36, 8),
    Sum.inr (37, 60), Sum.inr (34, 1),
    Sum.inr (34, 2), Sum.inr (37, 63)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket43Sign : Fin 64 → ℤ :=
  ![-1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1,
    -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1, -1, 1, 1, -1, 1, -1, -1, 1,
    -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket43Phase : Fin 64 → ZMod 2 :=
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
theorem generatedFifthXiShortPacket43_physical : ∀ e : Fin 64, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket43Source e)) i =
      2 * generatedFifthXiShortPacket43Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket43Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
