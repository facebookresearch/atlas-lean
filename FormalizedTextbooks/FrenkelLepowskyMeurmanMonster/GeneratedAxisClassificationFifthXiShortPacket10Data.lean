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
def generatedFifthXiShortPacket10Target (e : Fin 64) : generatedFifthXiShortCachedLabel :=
  Sum.inr (10, e)

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket10Source : Fin 64 → generatedFifthXiShortCachedLabel :=
  ![Sum.inl (1, ⟨(0, 4), by decide⟩), Sum.inr (10, 31),
    Sum.inr (10, 19), Sum.inl (1, ⟨(1, 4), by decide⟩),
    Sum.inr (10, 21), Sum.inl (1, ⟨(2, 4), by decide⟩),
    Sum.inl (0, ⟨(3, 4), by decide⟩), Sum.inr (10, 22),
    Sum.inr (10, 25), Sum.inl (1, ⟨(3, 4), by decide⟩),
    Sum.inl (0, ⟨(2, 4), by decide⟩), Sum.inr (10, 26),
    Sum.inl (0, ⟨(1, 4), by decide⟩), Sum.inr (10, 28),
    Sum.inr (10, 16), Sum.inl (0, ⟨(0, 4), by decide⟩),
    Sum.inl (1, ⟨(0, 6), by decide⟩), Sum.inr (10, 0),
    Sum.inr (10, 12), Sum.inl (1, ⟨(1, 6), by decide⟩),
    Sum.inr (10, 10), Sum.inl (1, ⟨(2, 6), by decide⟩),
    Sum.inl (0, ⟨(3, 6), by decide⟩), Sum.inr (10, 9),
    Sum.inr (10, 6), Sum.inl (1, ⟨(3, 6), by decide⟩),
    Sum.inl (0, ⟨(2, 6), by decide⟩), Sum.inr (10, 5),
    Sum.inl (0, ⟨(1, 6), by decide⟩), Sum.inr (10, 3),
    Sum.inr (10, 15), Sum.inl (0, ⟨(0, 6), by decide⟩),
    Sum.inl (0, ⟨(0, 7), by decide⟩), Sum.inr (10, 63),
    Sum.inr (10, 51), Sum.inl (0, ⟨(1, 7), by decide⟩),
    Sum.inr (10, 53), Sum.inl (0, ⟨(2, 7), by decide⟩),
    Sum.inl (1, ⟨(3, 7), by decide⟩), Sum.inr (10, 54),
    Sum.inr (10, 57), Sum.inl (0, ⟨(3, 7), by decide⟩),
    Sum.inl (1, ⟨(2, 7), by decide⟩), Sum.inr (10, 58),
    Sum.inl (1, ⟨(1, 7), by decide⟩), Sum.inr (10, 60),
    Sum.inr (10, 48), Sum.inl (1, ⟨(0, 7), by decide⟩),
    Sum.inl (1, ⟨(0, 5), by decide⟩), Sum.inr (10, 47),
    Sum.inr (10, 35), Sum.inl (1, ⟨(1, 5), by decide⟩),
    Sum.inr (10, 37), Sum.inl (1, ⟨(2, 5), by decide⟩),
    Sum.inl (0, ⟨(3, 5), by decide⟩), Sum.inr (10, 38),
    Sum.inr (10, 41), Sum.inl (1, ⟨(3, 5), by decide⟩),
    Sum.inl (0, ⟨(2, 5), by decide⟩), Sum.inr (10, 42),
    Sum.inl (0, ⟨(1, 5), by decide⟩), Sum.inr (10, 44),
    Sum.inr (10, 32), Sum.inl (0, ⟨(0, 5), by decide⟩)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket10Sign : Fin 64 → ℤ :=
  ![-1, 1, 1, -1, 1, -1, 1, 1, 1, -1, 1, 1,
    1, 1, 1, 1, -1, -1, -1, -1, -1, -1, 1, -1,
    -1, -1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1,
    1, -1, 1, 1, 1, -1, 1, 1, 1, 1, 1, 1,
    -1, 1, 1, -1, 1, -1, 1, 1, 1, -1, 1, 1,
    1, 1, 1, 1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket10Phase : Fin 64 → ZMod 2 :=
  ![0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1,
    1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1,
    0, 0, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0,
    0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1,
    1, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0,
    0, 0, 0, 1]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Check 64 genuine source/target vectors in all 24 physical coordinates.
/-- Every displayed physical source has the asserted exact integer Xi image. -/
theorem generatedFifthXiShortPacket10_physical : ∀ e : Fin 64, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket10Source e)) i =
      2 * generatedFifthXiShortPacket10Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket10Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
