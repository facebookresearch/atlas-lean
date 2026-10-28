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
def generatedFifthXiShortPacket11Target (e : Fin 64) : generatedFifthXiShortCachedLabel :=
  Sum.inr (11, e)

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket11Source : Fin 64 → generatedFifthXiShortCachedLabel :=
  ![Sum.inl (1, ⟨(0, 8), by decide⟩), Sum.inr (11, 31),
    Sum.inr (11, 19), Sum.inl (1, ⟨(1, 8), by decide⟩),
    Sum.inr (11, 21), Sum.inl (1, ⟨(2, 8), by decide⟩),
    Sum.inl (0, ⟨(3, 8), by decide⟩), Sum.inr (11, 22),
    Sum.inr (11, 25), Sum.inl (1, ⟨(3, 8), by decide⟩),
    Sum.inl (0, ⟨(2, 8), by decide⟩), Sum.inr (11, 26),
    Sum.inl (0, ⟨(1, 8), by decide⟩), Sum.inr (11, 28),
    Sum.inr (11, 16), Sum.inl (0, ⟨(0, 8), by decide⟩),
    Sum.inl (1, ⟨(0, 10), by decide⟩), Sum.inr (11, 0),
    Sum.inr (11, 12), Sum.inl (1, ⟨(1, 10), by decide⟩),
    Sum.inr (11, 10), Sum.inl (1, ⟨(2, 10), by decide⟩),
    Sum.inl (0, ⟨(3, 10), by decide⟩), Sum.inr (11, 9),
    Sum.inr (11, 6), Sum.inl (1, ⟨(3, 10), by decide⟩),
    Sum.inl (0, ⟨(2, 10), by decide⟩), Sum.inr (11, 5),
    Sum.inl (0, ⟨(1, 10), by decide⟩), Sum.inr (11, 3),
    Sum.inr (11, 15), Sum.inl (0, ⟨(0, 10), by decide⟩),
    Sum.inl (0, ⟨(0, 11), by decide⟩), Sum.inr (11, 63),
    Sum.inr (11, 51), Sum.inl (0, ⟨(1, 11), by decide⟩),
    Sum.inr (11, 53), Sum.inl (0, ⟨(2, 11), by decide⟩),
    Sum.inl (1, ⟨(3, 11), by decide⟩), Sum.inr (11, 54),
    Sum.inr (11, 57), Sum.inl (0, ⟨(3, 11), by decide⟩),
    Sum.inl (1, ⟨(2, 11), by decide⟩), Sum.inr (11, 58),
    Sum.inl (1, ⟨(1, 11), by decide⟩), Sum.inr (11, 60),
    Sum.inr (11, 48), Sum.inl (1, ⟨(0, 11), by decide⟩),
    Sum.inl (1, ⟨(0, 9), by decide⟩), Sum.inr (11, 47),
    Sum.inr (11, 35), Sum.inl (1, ⟨(1, 9), by decide⟩),
    Sum.inr (11, 37), Sum.inl (1, ⟨(2, 9), by decide⟩),
    Sum.inl (0, ⟨(3, 9), by decide⟩), Sum.inr (11, 38),
    Sum.inr (11, 41), Sum.inl (1, ⟨(3, 9), by decide⟩),
    Sum.inl (0, ⟨(2, 9), by decide⟩), Sum.inr (11, 42),
    Sum.inl (0, ⟨(1, 9), by decide⟩), Sum.inr (11, 44),
    Sum.inr (11, 32), Sum.inl (0, ⟨(0, 9), by decide⟩)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket11Sign : Fin 64 → ℤ :=
  ![-1, 1, 1, -1, 1, -1, 1, 1, 1, -1, 1, 1,
    1, 1, 1, 1, -1, -1, -1, -1, -1, -1, 1, -1,
    -1, -1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1,
    1, -1, 1, 1, 1, -1, 1, 1, 1, 1, 1, 1,
    -1, 1, 1, -1, 1, -1, 1, 1, 1, -1, 1, 1,
    1, 1, 1, 1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket11Phase : Fin 64 → ZMod 2 :=
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
theorem generatedFifthXiShortPacket11_physical : ∀ e : Fin 64, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket11Source e)) i =
      2 * generatedFifthXiShortPacket11Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket11Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
