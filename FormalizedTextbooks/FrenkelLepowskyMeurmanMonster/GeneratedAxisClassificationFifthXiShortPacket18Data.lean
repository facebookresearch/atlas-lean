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
def generatedFifthXiShortPacket18Target (e : Fin 64) : generatedFifthXiShortCachedLabel :=
  Sum.inr (18, e)

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket18Source : Fin 64 → generatedFifthXiShortCachedLabel :=
  ![Sum.inr (21, 31), Sum.inr (16, 34),
    Sum.inr (16, 33), Sum.inr (21, 28),
    Sum.inr (15, 40), Sum.inr (18, 21),
    Sum.inr (18, 22), Sum.inr (15, 43),
    Sum.inr (15, 36), Sum.inr (18, 25),
    Sum.inr (18, 26), Sum.inr (15, 39),
    Sum.inr (21, 19), Sum.inr (16, 46),
    Sum.inr (16, 45), Sum.inr (21, 16),
    Sum.inr (19, 0), Sum.inr (14, 61),
    Sum.inr (14, 62), Sum.inr (19, 3),
    Sum.inr (17, 55), Sum.inr (20, 10),
    Sum.inr (20, 9), Sum.inr (17, 52),
    Sum.inr (17, 59), Sum.inr (20, 6),
    Sum.inr (20, 5), Sum.inr (17, 56),
    Sum.inr (19, 12), Sum.inr (14, 49),
    Sum.inr (14, 50), Sum.inr (19, 15),
    Sum.inr (19, 48), Sum.inr (14, 13),
    Sum.inr (14, 14), Sum.inr (19, 51),
    Sum.inr (17, 7), Sum.inr (20, 58),
    Sum.inr (20, 57), Sum.inr (17, 4),
    Sum.inr (17, 11), Sum.inr (20, 54),
    Sum.inr (20, 53), Sum.inr (17, 8),
    Sum.inr (19, 60), Sum.inr (14, 1),
    Sum.inr (14, 2), Sum.inr (19, 63),
    Sum.inr (21, 47), Sum.inr (16, 18),
    Sum.inr (16, 17), Sum.inr (21, 44),
    Sum.inr (15, 24), Sum.inr (18, 37),
    Sum.inr (18, 38), Sum.inr (15, 27),
    Sum.inr (15, 20), Sum.inr (18, 41),
    Sum.inr (18, 42), Sum.inr (15, 23),
    Sum.inr (21, 35), Sum.inr (16, 30),
    Sum.inr (16, 29), Sum.inr (21, 32)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket18Sign : Fin 64 → ℤ :=
  ![1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1,
    1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1, 1, -1, -1, 1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1,
    1, -1, -1, 1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket18Phase : Fin 64 → ZMod 2 :=
  ![1, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0,
    0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1,
    0, 0, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0,
    0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1,
    0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1,
    1, 1, 1, 0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Check 64 genuine source/target vectors in all 24 physical coordinates.
/-- Every displayed physical source has the asserted exact integer Xi image. -/
theorem generatedFifthXiShortPacket18_physical : ∀ e : Fin 64, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket18Source e)) i =
      2 * generatedFifthXiShortPacket18Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket18Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
