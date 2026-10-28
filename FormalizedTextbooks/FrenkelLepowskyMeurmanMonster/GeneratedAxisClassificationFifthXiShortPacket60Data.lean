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
def generatedFifthXiShortPacket60Target (e : Fin 16) : generatedFifthXiShortCachedLabel :=
  (![Sum.inl (0, ⟨(18, 22), by decide⟩), Sum.inl (1, ⟨(18, 22), by decide⟩),
    Sum.inl (0, ⟨(18, 23), by decide⟩), Sum.inl (1, ⟨(18, 23), by decide⟩),
    Sum.inl (0, ⟨(19, 20), by decide⟩), Sum.inl (1, ⟨(19, 20), by decide⟩),
    Sum.inl (0, ⟨(19, 21), by decide⟩), Sum.inl (1, ⟨(19, 21), by decide⟩),
    Sum.inl (0, ⟨(19, 22), by decide⟩), Sum.inl (1, ⟨(19, 22), by decide⟩),
    Sum.inl (0, ⟨(19, 23), by decide⟩), Sum.inl (1, ⟨(19, 23), by decide⟩),
    Sum.inl (0, ⟨(20, 22), by decide⟩), Sum.inl (1, ⟨(20, 22), by decide⟩),
    Sum.inl (0, ⟨(21, 23), by decide⟩), Sum.inl (1, ⟨(21, 23), by decide⟩)]) e

set_option maxRecDepth 10000 in
/-- Actual inverse-Xi source rows, in the genuine short dictionary. -/
def generatedFifthXiShortPacket60Source : Fin 16 → generatedFifthXiShortCachedLabel :=
  ![Sum.inr (22, 11), Sum.inr (22, 4),
    Sum.inr (22, 52), Sum.inr (22, 59),
    Sum.inr (22, 24), Sum.inr (22, 23),
    Sum.inr (22, 39), Sum.inr (22, 40),
    Sum.inr (22, 7), Sum.inr (22, 8),
    Sum.inr (22, 56), Sum.inr (22, 55),
    Sum.inl (1, ⟨(21, 23), by decide⟩), Sum.inl (0, ⟨(20, 22), by decide⟩),
    Sum.inl (0, ⟨(21, 23), by decide⟩), Sum.inl (1, ⟨(20, 22), by decide⟩)]

/-- The actual global physical signs of the inverse images. -/
def generatedFifthXiShortPacket60Sign : Fin 16 → ℤ :=
  ![1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1,
    1, -1, 1, -1]

/-- Actual full preferred-Q phases, including the central Q correction. -/
def generatedFifthXiShortPacket60Phase : Fin 16 → ZMod 2 :=
  ![1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0,
    0, 1, 0, 1]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Check 16 genuine source/target vectors in all 24 physical coordinates.
/-- Every displayed physical source has the asserted exact integer Xi image. -/
theorem generatedFifthXiShortPacket60_physical : ∀ e : Fin 16, ∀ i : Fin 24,
    (co1XiNumerator *ᵥ
      generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket60Source e)) i =
      2 * generatedFifthXiShortPacket60Sign e *
        generatedFifthXiShortCachedIntegral (generatedFifthXiShortPacket60Target e) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
