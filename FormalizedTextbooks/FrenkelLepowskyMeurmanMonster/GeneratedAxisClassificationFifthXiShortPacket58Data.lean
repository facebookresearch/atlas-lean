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
def generatedFifthXiShortPacket58Target (e : Fin 64) : generatedFifthXiShortCachedLabel :=
  (![Sum.inl (0, ⟨(4, 6), by decide⟩), Sum.inl (1, ⟨(4, 6), by decide⟩),
    Sum.inl (0, ⟨(4, 16), by decide⟩), Sum.inl (1, ⟨(4, 16), by decide⟩),
    Sum.inl (0, ⟨(4, 17), by decide⟩), Sum.inl (1, ⟨(4, 17), by decide⟩),
    Sum.inl (0, ⟨(4, 18), by decide⟩), Sum.inl (1, ⟨(4, 18), by decide⟩),
    Sum.inl (0, ⟨(4, 19), by decide⟩), Sum.inl (1, ⟨(4, 19), by decide⟩),
    Sum.inl (0, ⟨(5, 7), by decide⟩), Sum.inl (1, ⟨(5, 7), by decide⟩),
    Sum.inl (0, ⟨(5, 16), by decide⟩), Sum.inl (1, ⟨(5, 16), by decide⟩),
    Sum.inl (0, ⟨(5, 17), by decide⟩), Sum.inl (1, ⟨(5, 17), by decide⟩),
    Sum.inl (0, ⟨(5, 18), by decide⟩), Sum.inl (1, ⟨(5, 18), by decide⟩),
    Sum.inl (0, ⟨(5, 19), by decide⟩), Sum.inl (1, ⟨(5, 19), by decide⟩),
    Sum.inl (0, ⟨(6, 16), by decide⟩), Sum.inl (1, ⟨(6, 16), by decide⟩),
    Sum.inl (0, ⟨(6, 17), by decide⟩), Sum.inl (1, ⟨(6, 17), by decide⟩),
    Sum.inl (0, ⟨(6, 18), by decide⟩), Sum.inl (1, ⟨(6, 18), by decide⟩),
    Sum.inl (0, ⟨(6, 19), by decide⟩), Sum.inl (1, ⟨(6, 19), by decide⟩),
    Sum.inl (0, ⟨(7, 16), by decide⟩), Sum.inl (1, ⟨(7, 16), by decide⟩),
    Sum.inl (0, ⟨(7, 17), by decide⟩), Sum.inl (1, ⟨(7, 17), by decide⟩),
    Sum.inl (0, ⟨(7, 18), by decide⟩), Sum.inl (1, ⟨(7, 18), by decide⟩),
    Sum.inl (0, ⟨(7, 19), by decide⟩), Sum.inl (1, ⟨(7, 19), by decide⟩),
    Sum.inl (0, ⟨(8, 11), by decide⟩), Sum.inl (1, ⟨(8, 11), by decide⟩),
    Sum.inl (0, ⟨(8, 16), by decide⟩), Sum.inl (1, ⟨(8, 16), by decide⟩),
    Sum.inl (0, ⟨(8, 17), by decide⟩), Sum.inl (1, ⟨(8, 17), by decide⟩),
    Sum.inl (0, ⟨(8, 18), by decide⟩), Sum.inl (1, ⟨(8, 18), by decide⟩),
    Sum.inl (0, ⟨(8, 19), by decide⟩), Sum.inl (1, ⟨(8, 19), by decide⟩),
    Sum.inl (0, ⟨(9, 10), by decide⟩), Sum.inl (1, ⟨(9, 10), by decide⟩),
    Sum.inl (0, ⟨(9, 16), by decide⟩), Sum.inl (1, ⟨(9, 16), by decide⟩),
    Sum.inl (0, ⟨(9, 17), by decide⟩), Sum.inl (1, ⟨(9, 17), by decide⟩),
    Sum.inl (0, ⟨(9, 18), by decide⟩), Sum.inl (1, ⟨(9, 18), by decide⟩),
    Sum.inl (0, ⟨(9, 19), by decide⟩), Sum.inl (1, ⟨(9, 19), by decide⟩),
    Sum.inl (0, ⟨(10, 16), by decide⟩), Sum.inl (1, ⟨(10, 16), by decide⟩),
    Sum.inl (0, ⟨(10, 17), by decide⟩), Sum.inl (1, ⟨(10, 17), by decide⟩),
    Sum.inl (0, ⟨(10, 18), by decide⟩), Sum.inl (1, ⟨(10, 18), by decide⟩),
    Sum.inl (0, ⟨(10, 19), by decide⟩), Sum.inl (1, ⟨(10, 19), by decide⟩)]) e

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket58Source : Fin 64 → generatedFifthXiShortCachedLabel :=
  ![Sum.inl (1, ⟨(5, 7), by decide⟩), Sum.inl (0, ⟨(4, 6), by decide⟩),
    Sum.inr (1, 30), Sum.inr (1, 17),
    Sum.inr (1, 33), Sum.inr (1, 46),
    Sum.inr (1, 1), Sum.inr (1, 14),
    Sum.inr (1, 62), Sum.inr (1, 49),
    Sum.inl (0, ⟨(5, 7), by decide⟩), Sum.inl (1, ⟨(4, 6), by decide⟩),
    Sum.inr (1, 18), Sum.inr (1, 29),
    Sum.inr (1, 45), Sum.inr (1, 34),
    Sum.inr (1, 13), Sum.inr (1, 2),
    Sum.inr (1, 50), Sum.inr (1, 61),
    Sum.inr (1, 20), Sum.inr (1, 27),
    Sum.inr (1, 43), Sum.inr (1, 36),
    Sum.inr (1, 11), Sum.inr (1, 4),
    Sum.inr (1, 52), Sum.inr (1, 59),
    Sum.inr (1, 24), Sum.inr (1, 23),
    Sum.inr (1, 39), Sum.inr (1, 40),
    Sum.inr (1, 7), Sum.inr (1, 8),
    Sum.inr (1, 56), Sum.inr (1, 55),
    Sum.inl (1, ⟨(9, 10), by decide⟩), Sum.inl (0, ⟨(8, 11), by decide⟩),
    Sum.inr (0, 30), Sum.inr (0, 17),
    Sum.inr (0, 33), Sum.inr (0, 46),
    Sum.inr (0, 1), Sum.inr (0, 14),
    Sum.inr (0, 62), Sum.inr (0, 49),
    Sum.inl (0, ⟨(9, 10), by decide⟩), Sum.inl (1, ⟨(8, 11), by decide⟩),
    Sum.inr (0, 18), Sum.inr (0, 29),
    Sum.inr (0, 45), Sum.inr (0, 34),
    Sum.inr (0, 13), Sum.inr (0, 2),
    Sum.inr (0, 50), Sum.inr (0, 61),
    Sum.inr (0, 20), Sum.inr (0, 27),
    Sum.inr (0, 43), Sum.inr (0, 36),
    Sum.inr (0, 11), Sum.inr (0, 4),
    Sum.inr (0, 52), Sum.inr (0, 59)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket58Sign : Fin 64 → ℤ :=
  ![1, -1, -1, 1, 1, -1, 1, -1, -1, 1, 1, -1,
    -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1,
    1, -1, -1, 1, 1, -1, 1, -1, -1, 1, 1, -1,
    -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1,
    1, -1, -1, 1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket58Phase : Fin 64 → ZMod 2 :=
  ![0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
    0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
    0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
    0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1,
    1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0,
    1, 0, 1, 0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Check 64 genuine source/target vectors in all 24 physical coordinates.
/-- Every displayed physical source has the asserted exact integer Xi image. -/
theorem generatedFifthXiShortPacket58_physical : ∀ e : Fin 64, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket58Source e)) i =
      2 * generatedFifthXiShortPacket58Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket58Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
