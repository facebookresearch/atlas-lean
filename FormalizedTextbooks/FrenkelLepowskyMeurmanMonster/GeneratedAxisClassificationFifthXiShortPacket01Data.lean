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
def generatedFifthXiShortPacket01Target (e : Fin 64) : generatedFifthXiShortCachedLabel :=
  Sum.inr (1, e)

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket01Source : Fin 64 → generatedFifthXiShortCachedLabel :=
  ![Sum.inl (1, ⟨(4, 16), by decide⟩), Sum.inr (1, 31),
    Sum.inr (1, 19), Sum.inl (1, ⟨(5, 16), by decide⟩),
    Sum.inr (1, 21), Sum.inl (1, ⟨(6, 16), by decide⟩),
    Sum.inl (0, ⟨(7, 16), by decide⟩), Sum.inr (1, 22),
    Sum.inr (1, 25), Sum.inl (1, ⟨(7, 16), by decide⟩),
    Sum.inl (0, ⟨(6, 16), by decide⟩), Sum.inr (1, 26),
    Sum.inl (0, ⟨(5, 16), by decide⟩), Sum.inr (1, 28),
    Sum.inr (1, 16), Sum.inl (0, ⟨(4, 16), by decide⟩),
    Sum.inl (1, ⟨(4, 18), by decide⟩), Sum.inr (1, 0),
    Sum.inr (1, 12), Sum.inl (1, ⟨(5, 18), by decide⟩),
    Sum.inr (1, 10), Sum.inl (1, ⟨(6, 18), by decide⟩),
    Sum.inl (0, ⟨(7, 18), by decide⟩), Sum.inr (1, 9),
    Sum.inr (1, 6), Sum.inl (1, ⟨(7, 18), by decide⟩),
    Sum.inl (0, ⟨(6, 18), by decide⟩), Sum.inr (1, 5),
    Sum.inl (0, ⟨(5, 18), by decide⟩), Sum.inr (1, 3),
    Sum.inr (1, 15), Sum.inl (0, ⟨(4, 18), by decide⟩),
    Sum.inl (0, ⟨(4, 19), by decide⟩), Sum.inr (1, 63),
    Sum.inr (1, 51), Sum.inl (0, ⟨(5, 19), by decide⟩),
    Sum.inr (1, 53), Sum.inl (0, ⟨(6, 19), by decide⟩),
    Sum.inl (1, ⟨(7, 19), by decide⟩), Sum.inr (1, 54),
    Sum.inr (1, 57), Sum.inl (0, ⟨(7, 19), by decide⟩),
    Sum.inl (1, ⟨(6, 19), by decide⟩), Sum.inr (1, 58),
    Sum.inl (1, ⟨(5, 19), by decide⟩), Sum.inr (1, 60),
    Sum.inr (1, 48), Sum.inl (1, ⟨(4, 19), by decide⟩),
    Sum.inl (1, ⟨(4, 17), by decide⟩), Sum.inr (1, 47),
    Sum.inr (1, 35), Sum.inl (1, ⟨(5, 17), by decide⟩),
    Sum.inr (1, 37), Sum.inl (1, ⟨(6, 17), by decide⟩),
    Sum.inl (0, ⟨(7, 17), by decide⟩), Sum.inr (1, 38),
    Sum.inr (1, 41), Sum.inl (1, ⟨(7, 17), by decide⟩),
    Sum.inl (0, ⟨(6, 17), by decide⟩), Sum.inr (1, 42),
    Sum.inl (0, ⟨(5, 17), by decide⟩), Sum.inr (1, 44),
    Sum.inr (1, 32), Sum.inl (0, ⟨(4, 17), by decide⟩)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket01Sign : Fin 64 → ℤ :=
  ![-1, 1, 1, -1, 1, -1, 1, 1, 1, -1, 1, 1,
    1, 1, 1, 1, -1, -1, -1, -1, -1, -1, 1, -1,
    -1, -1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1,
    1, -1, 1, 1, 1, -1, 1, 1, 1, 1, 1, 1,
    -1, 1, 1, -1, 1, -1, 1, 1, 1, -1, 1, 1,
    1, 1, 1, 1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket01Phase : Fin 64 → ZMod 2 :=
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
theorem generatedFifthXiShortPacket01_physical : ∀ e : Fin 64, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket01Source e)) i =
      2 * generatedFifthXiShortPacket01Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket01Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
