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
def generatedFifthXiShortPacket23Target (e : Fin 64) : generatedFifthXiShortCachedLabel :=
  Sum.inr (23, e)

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket23Source : Fin 64 → generatedFifthXiShortCachedLabel :=
  ![Sum.inl (1, ⟨(0, 12), by decide⟩), Sum.inr (23, 31),
    Sum.inr (23, 19), Sum.inl (1, ⟨(1, 12), by decide⟩),
    Sum.inr (23, 21), Sum.inl (1, ⟨(2, 12), by decide⟩),
    Sum.inl (0, ⟨(3, 12), by decide⟩), Sum.inr (23, 22),
    Sum.inr (23, 25), Sum.inl (1, ⟨(3, 12), by decide⟩),
    Sum.inl (0, ⟨(2, 12), by decide⟩), Sum.inr (23, 26),
    Sum.inl (0, ⟨(1, 12), by decide⟩), Sum.inr (23, 28),
    Sum.inr (23, 16), Sum.inl (0, ⟨(0, 12), by decide⟩),
    Sum.inl (1, ⟨(0, 14), by decide⟩), Sum.inr (23, 0),
    Sum.inr (23, 12), Sum.inl (1, ⟨(1, 14), by decide⟩),
    Sum.inr (23, 10), Sum.inl (1, ⟨(2, 14), by decide⟩),
    Sum.inl (0, ⟨(3, 14), by decide⟩), Sum.inr (23, 9),
    Sum.inr (23, 6), Sum.inl (1, ⟨(3, 14), by decide⟩),
    Sum.inl (0, ⟨(2, 14), by decide⟩), Sum.inr (23, 5),
    Sum.inl (0, ⟨(1, 14), by decide⟩), Sum.inr (23, 3),
    Sum.inr (23, 15), Sum.inl (0, ⟨(0, 14), by decide⟩),
    Sum.inl (0, ⟨(0, 15), by decide⟩), Sum.inr (23, 63),
    Sum.inr (23, 51), Sum.inl (0, ⟨(1, 15), by decide⟩),
    Sum.inr (23, 53), Sum.inl (0, ⟨(2, 15), by decide⟩),
    Sum.inl (1, ⟨(3, 15), by decide⟩), Sum.inr (23, 54),
    Sum.inr (23, 57), Sum.inl (0, ⟨(3, 15), by decide⟩),
    Sum.inl (1, ⟨(2, 15), by decide⟩), Sum.inr (23, 58),
    Sum.inl (1, ⟨(1, 15), by decide⟩), Sum.inr (23, 60),
    Sum.inr (23, 48), Sum.inl (1, ⟨(0, 15), by decide⟩),
    Sum.inl (1, ⟨(0, 13), by decide⟩), Sum.inr (23, 47),
    Sum.inr (23, 35), Sum.inl (1, ⟨(1, 13), by decide⟩),
    Sum.inr (23, 37), Sum.inl (1, ⟨(2, 13), by decide⟩),
    Sum.inl (0, ⟨(3, 13), by decide⟩), Sum.inr (23, 38),
    Sum.inr (23, 41), Sum.inl (1, ⟨(3, 13), by decide⟩),
    Sum.inl (0, ⟨(2, 13), by decide⟩), Sum.inr (23, 42),
    Sum.inl (0, ⟨(1, 13), by decide⟩), Sum.inr (23, 44),
    Sum.inr (23, 32), Sum.inl (0, ⟨(0, 13), by decide⟩)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket23Sign : Fin 64 → ℤ :=
  ![-1, 1, 1, -1, 1, -1, 1, 1, 1, -1, 1, 1,
    1, 1, 1, 1, -1, -1, -1, -1, -1, -1, 1, -1,
    -1, -1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1,
    1, -1, 1, 1, 1, -1, 1, 1, 1, 1, 1, 1,
    -1, 1, 1, -1, 1, -1, 1, 1, 1, -1, 1, 1,
    1, 1, 1, 1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket23Phase : Fin 64 → ZMod 2 :=
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
theorem generatedFifthXiShortPacket23_physical : ∀ e : Fin 64, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket23Source e)) i =
      2 * generatedFifthXiShortPacket23Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket23Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
