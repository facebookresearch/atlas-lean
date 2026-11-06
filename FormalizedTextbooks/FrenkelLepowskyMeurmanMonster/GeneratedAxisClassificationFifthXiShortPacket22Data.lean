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
def generatedFifthXiShortPacket22Target (e : Fin 64) : generatedFifthXiShortCachedLabel :=
  Sum.inr (22, e)

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket22Source : Fin 64 → generatedFifthXiShortCachedLabel :=
  ![Sum.inl (1, ⟨(16, 20), by decide⟩), Sum.inr (22, 31),
    Sum.inr (22, 19), Sum.inl (1, ⟨(17, 20), by decide⟩),
    Sum.inr (22, 21), Sum.inl (1, ⟨(18, 20), by decide⟩),
    Sum.inl (0, ⟨(19, 20), by decide⟩), Sum.inr (22, 22),
    Sum.inr (22, 25), Sum.inl (1, ⟨(19, 20), by decide⟩),
    Sum.inl (0, ⟨(18, 20), by decide⟩), Sum.inr (22, 26),
    Sum.inl (0, ⟨(17, 20), by decide⟩), Sum.inr (22, 28),
    Sum.inr (22, 16), Sum.inl (0, ⟨(16, 20), by decide⟩),
    Sum.inl (1, ⟨(16, 22), by decide⟩), Sum.inr (22, 0),
    Sum.inr (22, 12), Sum.inl (1, ⟨(17, 22), by decide⟩),
    Sum.inr (22, 10), Sum.inl (1, ⟨(18, 22), by decide⟩),
    Sum.inl (0, ⟨(19, 22), by decide⟩), Sum.inr (22, 9),
    Sum.inr (22, 6), Sum.inl (1, ⟨(19, 22), by decide⟩),
    Sum.inl (0, ⟨(18, 22), by decide⟩), Sum.inr (22, 5),
    Sum.inl (0, ⟨(17, 22), by decide⟩), Sum.inr (22, 3),
    Sum.inr (22, 15), Sum.inl (0, ⟨(16, 22), by decide⟩),
    Sum.inl (0, ⟨(16, 23), by decide⟩), Sum.inr (22, 63),
    Sum.inr (22, 51), Sum.inl (0, ⟨(17, 23), by decide⟩),
    Sum.inr (22, 53), Sum.inl (0, ⟨(18, 23), by decide⟩),
    Sum.inl (1, ⟨(19, 23), by decide⟩), Sum.inr (22, 54),
    Sum.inr (22, 57), Sum.inl (0, ⟨(19, 23), by decide⟩),
    Sum.inl (1, ⟨(18, 23), by decide⟩), Sum.inr (22, 58),
    Sum.inl (1, ⟨(17, 23), by decide⟩), Sum.inr (22, 60),
    Sum.inr (22, 48), Sum.inl (1, ⟨(16, 23), by decide⟩),
    Sum.inl (1, ⟨(16, 21), by decide⟩), Sum.inr (22, 47),
    Sum.inr (22, 35), Sum.inl (1, ⟨(17, 21), by decide⟩),
    Sum.inr (22, 37), Sum.inl (1, ⟨(18, 21), by decide⟩),
    Sum.inl (0, ⟨(19, 21), by decide⟩), Sum.inr (22, 38),
    Sum.inr (22, 41), Sum.inl (1, ⟨(19, 21), by decide⟩),
    Sum.inl (0, ⟨(18, 21), by decide⟩), Sum.inr (22, 42),
    Sum.inl (0, ⟨(17, 21), by decide⟩), Sum.inr (22, 44),
    Sum.inr (22, 32), Sum.inl (0, ⟨(16, 21), by decide⟩)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket22Sign : Fin 64 → ℤ :=
  ![-1, 1, 1, -1, 1, -1, 1, 1, 1, -1, 1, 1,
    1, 1, 1, 1, -1, -1, -1, -1, -1, -1, 1, -1,
    -1, -1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1,
    1, -1, 1, 1, 1, -1, 1, 1, 1, 1, 1, 1,
    -1, 1, 1, -1, 1, -1, 1, 1, 1, -1, 1, 1,
    1, 1, 1, 1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket22Phase : Fin 64 → ZMod 2 :=
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
theorem generatedFifthXiShortPacket22_physical : ∀ e : Fin 64, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket22Source e)) i =
      2 * generatedFifthXiShortPacket22Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket22Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
