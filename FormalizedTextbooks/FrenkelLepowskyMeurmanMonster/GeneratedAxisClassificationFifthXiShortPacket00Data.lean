/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthXiShortCache

/-! First bounded packet of actual physical Xi preferred-short transport. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Actual target rows of the first outgoing octad family. -/
def generatedFifthXiShortPacket00Target (e : Fin 64) : generatedFifthXiShortCachedLabel :=
  Sum.inr (0, e)

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket00Source : Fin 64 → generatedFifthXiShortCachedLabel :=
  ![Sum.inl (1, ⟨(8, 16), by decide⟩), Sum.inr (0, 31),
    Sum.inr (0, 19), Sum.inl (1, ⟨(9, 16), by decide⟩),
    Sum.inr (0, 21), Sum.inl (1, ⟨(10, 16), by decide⟩),
    Sum.inl (0, ⟨(11, 16), by decide⟩), Sum.inr (0, 22),
    Sum.inr (0, 25), Sum.inl (1, ⟨(11, 16), by decide⟩),
    Sum.inl (0, ⟨(10, 16), by decide⟩), Sum.inr (0, 26),
    Sum.inl (0, ⟨(9, 16), by decide⟩), Sum.inr (0, 28),
    Sum.inr (0, 16), Sum.inl (0, ⟨(8, 16), by decide⟩),
    Sum.inl (1, ⟨(8, 18), by decide⟩), Sum.inr (0, 0),
    Sum.inr (0, 12), Sum.inl (1, ⟨(9, 18), by decide⟩),
    Sum.inr (0, 10), Sum.inl (1, ⟨(10, 18), by decide⟩),
    Sum.inl (0, ⟨(11, 18), by decide⟩), Sum.inr (0, 9),
    Sum.inr (0, 6), Sum.inl (1, ⟨(11, 18), by decide⟩),
    Sum.inl (0, ⟨(10, 18), by decide⟩), Sum.inr (0, 5),
    Sum.inl (0, ⟨(9, 18), by decide⟩), Sum.inr (0, 3),
    Sum.inr (0, 15), Sum.inl (0, ⟨(8, 18), by decide⟩),
    Sum.inl (0, ⟨(8, 19), by decide⟩), Sum.inr (0, 63),
    Sum.inr (0, 51), Sum.inl (0, ⟨(9, 19), by decide⟩),
    Sum.inr (0, 53), Sum.inl (0, ⟨(10, 19), by decide⟩),
    Sum.inl (1, ⟨(11, 19), by decide⟩), Sum.inr (0, 54),
    Sum.inr (0, 57), Sum.inl (0, ⟨(11, 19), by decide⟩),
    Sum.inl (1, ⟨(10, 19), by decide⟩), Sum.inr (0, 58),
    Sum.inl (1, ⟨(9, 19), by decide⟩), Sum.inr (0, 60),
    Sum.inr (0, 48), Sum.inl (1, ⟨(8, 19), by decide⟩),
    Sum.inl (1, ⟨(8, 17), by decide⟩), Sum.inr (0, 47),
    Sum.inr (0, 35), Sum.inl (1, ⟨(9, 17), by decide⟩),
    Sum.inr (0, 37), Sum.inl (1, ⟨(10, 17), by decide⟩),
    Sum.inl (0, ⟨(11, 17), by decide⟩), Sum.inr (0, 38),
    Sum.inr (0, 41), Sum.inl (1, ⟨(11, 17), by decide⟩),
    Sum.inl (0, ⟨(10, 17), by decide⟩), Sum.inr (0, 42),
    Sum.inl (0, ⟨(9, 17), by decide⟩), Sum.inr (0, 44),
    Sum.inr (0, 32), Sum.inl (0, ⟨(8, 17), by decide⟩)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket00Sign : Fin 64 → ℤ :=
  ![-1, 1, 1, -1, 1, -1, 1, 1, 1, -1, 1, 1,
    1, 1, 1, 1, -1, -1, -1, -1, -1, -1, 1, -1,
    -1, -1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1,
    1, -1, 1, 1, 1, -1, 1, 1, 1, 1, 1, 1,
    -1, 1, 1, -1, 1, -1, 1, 1, 1, -1, 1, 1,
    1, 1, 1, 1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket00Phase : Fin 64 → ZMod 2 :=
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
theorem generatedFifthXiShortPacket00_physical : ∀ e : Fin 64, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket00Source e)) i =
      2 * generatedFifthXiShortPacket00Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket00Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
