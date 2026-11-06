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
def generatedFifthXiShortPacket12Target (e : Fin 64) : generatedFifthXiShortCachedLabel :=
  Sum.inr (12, e)

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket12Source : Fin 64 → generatedFifthXiShortCachedLabel :=
  ![Sum.inl (1, ⟨(12, 16), by decide⟩), Sum.inr (12, 31),
    Sum.inr (12, 19), Sum.inl (1, ⟨(13, 16), by decide⟩),
    Sum.inr (12, 21), Sum.inl (1, ⟨(14, 16), by decide⟩),
    Sum.inl (0, ⟨(15, 16), by decide⟩), Sum.inr (12, 22),
    Sum.inr (12, 25), Sum.inl (1, ⟨(15, 16), by decide⟩),
    Sum.inl (0, ⟨(14, 16), by decide⟩), Sum.inr (12, 26),
    Sum.inl (0, ⟨(13, 16), by decide⟩), Sum.inr (12, 28),
    Sum.inr (12, 16), Sum.inl (0, ⟨(12, 16), by decide⟩),
    Sum.inl (1, ⟨(12, 18), by decide⟩), Sum.inr (12, 0),
    Sum.inr (12, 12), Sum.inl (1, ⟨(13, 18), by decide⟩),
    Sum.inr (12, 10), Sum.inl (1, ⟨(14, 18), by decide⟩),
    Sum.inl (0, ⟨(15, 18), by decide⟩), Sum.inr (12, 9),
    Sum.inr (12, 6), Sum.inl (1, ⟨(15, 18), by decide⟩),
    Sum.inl (0, ⟨(14, 18), by decide⟩), Sum.inr (12, 5),
    Sum.inl (0, ⟨(13, 18), by decide⟩), Sum.inr (12, 3),
    Sum.inr (12, 15), Sum.inl (0, ⟨(12, 18), by decide⟩),
    Sum.inl (0, ⟨(12, 19), by decide⟩), Sum.inr (12, 63),
    Sum.inr (12, 51), Sum.inl (0, ⟨(13, 19), by decide⟩),
    Sum.inr (12, 53), Sum.inl (0, ⟨(14, 19), by decide⟩),
    Sum.inl (1, ⟨(15, 19), by decide⟩), Sum.inr (12, 54),
    Sum.inr (12, 57), Sum.inl (0, ⟨(15, 19), by decide⟩),
    Sum.inl (1, ⟨(14, 19), by decide⟩), Sum.inr (12, 58),
    Sum.inl (1, ⟨(13, 19), by decide⟩), Sum.inr (12, 60),
    Sum.inr (12, 48), Sum.inl (1, ⟨(12, 19), by decide⟩),
    Sum.inl (1, ⟨(12, 17), by decide⟩), Sum.inr (12, 47),
    Sum.inr (12, 35), Sum.inl (1, ⟨(13, 17), by decide⟩),
    Sum.inr (12, 37), Sum.inl (1, ⟨(14, 17), by decide⟩),
    Sum.inl (0, ⟨(15, 17), by decide⟩), Sum.inr (12, 38),
    Sum.inr (12, 41), Sum.inl (1, ⟨(15, 17), by decide⟩),
    Sum.inl (0, ⟨(14, 17), by decide⟩), Sum.inr (12, 42),
    Sum.inl (0, ⟨(13, 17), by decide⟩), Sum.inr (12, 44),
    Sum.inr (12, 32), Sum.inl (0, ⟨(12, 17), by decide⟩)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket12Sign : Fin 64 → ℤ :=
  ![-1, 1, 1, -1, 1, -1, 1, 1, 1, -1, 1, 1,
    1, 1, 1, 1, -1, -1, -1, -1, -1, -1, 1, -1,
    -1, -1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1,
    1, -1, 1, 1, 1, -1, 1, 1, 1, 1, 1, 1,
    -1, 1, 1, -1, 1, -1, 1, 1, 1, -1, 1, 1,
    1, 1, 1, 1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket12Phase : Fin 64 → ZMod 2 :=
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
theorem generatedFifthXiShortPacket12_physical : ∀ e : Fin 64, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket12Source e)) i =
      2 * generatedFifthXiShortPacket12Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket12Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
