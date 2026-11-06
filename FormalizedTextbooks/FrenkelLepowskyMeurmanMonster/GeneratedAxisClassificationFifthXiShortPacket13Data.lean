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
def generatedFifthXiShortPacket13Target (e : Fin 64) : generatedFifthXiShortCachedLabel :=
  Sum.inr (13, e)

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket13Source : Fin 64 → generatedFifthXiShortCachedLabel :=
  ![Sum.inl (1, ⟨(0, 20), by decide⟩), Sum.inr (13, 31),
    Sum.inr (13, 19), Sum.inl (1, ⟨(1, 20), by decide⟩),
    Sum.inr (13, 21), Sum.inl (1, ⟨(2, 20), by decide⟩),
    Sum.inl (0, ⟨(3, 20), by decide⟩), Sum.inr (13, 22),
    Sum.inr (13, 25), Sum.inl (1, ⟨(3, 20), by decide⟩),
    Sum.inl (0, ⟨(2, 20), by decide⟩), Sum.inr (13, 26),
    Sum.inl (0, ⟨(1, 20), by decide⟩), Sum.inr (13, 28),
    Sum.inr (13, 16), Sum.inl (0, ⟨(0, 20), by decide⟩),
    Sum.inl (1, ⟨(0, 22), by decide⟩), Sum.inr (13, 0),
    Sum.inr (13, 12), Sum.inl (1, ⟨(1, 22), by decide⟩),
    Sum.inr (13, 10), Sum.inl (1, ⟨(2, 22), by decide⟩),
    Sum.inl (0, ⟨(3, 22), by decide⟩), Sum.inr (13, 9),
    Sum.inr (13, 6), Sum.inl (1, ⟨(3, 22), by decide⟩),
    Sum.inl (0, ⟨(2, 22), by decide⟩), Sum.inr (13, 5),
    Sum.inl (0, ⟨(1, 22), by decide⟩), Sum.inr (13, 3),
    Sum.inr (13, 15), Sum.inl (0, ⟨(0, 22), by decide⟩),
    Sum.inl (0, ⟨(0, 23), by decide⟩), Sum.inr (13, 63),
    Sum.inr (13, 51), Sum.inl (0, ⟨(1, 23), by decide⟩),
    Sum.inr (13, 53), Sum.inl (0, ⟨(2, 23), by decide⟩),
    Sum.inl (1, ⟨(3, 23), by decide⟩), Sum.inr (13, 54),
    Sum.inr (13, 57), Sum.inl (0, ⟨(3, 23), by decide⟩),
    Sum.inl (1, ⟨(2, 23), by decide⟩), Sum.inr (13, 58),
    Sum.inl (1, ⟨(1, 23), by decide⟩), Sum.inr (13, 60),
    Sum.inr (13, 48), Sum.inl (1, ⟨(0, 23), by decide⟩),
    Sum.inl (1, ⟨(0, 21), by decide⟩), Sum.inr (13, 47),
    Sum.inr (13, 35), Sum.inl (1, ⟨(1, 21), by decide⟩),
    Sum.inr (13, 37), Sum.inl (1, ⟨(2, 21), by decide⟩),
    Sum.inl (0, ⟨(3, 21), by decide⟩), Sum.inr (13, 38),
    Sum.inr (13, 41), Sum.inl (1, ⟨(3, 21), by decide⟩),
    Sum.inl (0, ⟨(2, 21), by decide⟩), Sum.inr (13, 42),
    Sum.inl (0, ⟨(1, 21), by decide⟩), Sum.inr (13, 44),
    Sum.inr (13, 32), Sum.inl (0, ⟨(0, 21), by decide⟩)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket13Sign : Fin 64 → ℤ :=
  ![-1, 1, 1, -1, 1, -1, 1, 1, 1, -1, 1, 1,
    1, 1, 1, 1, -1, -1, -1, -1, -1, -1, 1, -1,
    -1, -1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1,
    1, -1, 1, 1, 1, -1, 1, 1, 1, 1, 1, 1,
    -1, 1, 1, -1, 1, -1, 1, 1, 1, -1, 1, 1,
    1, 1, 1, 1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket13Phase : Fin 64 → ZMod 2 :=
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
theorem generatedFifthXiShortPacket13_physical : ∀ e : Fin 64, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket13Source e)) i =
      2 * generatedFifthXiShortPacket13Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket13Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
