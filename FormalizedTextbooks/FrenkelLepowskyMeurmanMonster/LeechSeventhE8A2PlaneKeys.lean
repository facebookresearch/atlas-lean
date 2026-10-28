/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhE8A2PlaneData
public import Mathlib.Order.Fin.Basic

/-! Finite lexicographic keys distinguish the original A2 root triples. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The ordinary base-120 lexicographic key of a candidate's three root-line indices. -/
def leechSeventhE8A2PlaneKey (p : Fin 1120) : ℕ :=
  (leechSeventhE8A2Indices p 0).val * 14400 +
    (leechSeventhE8A2Indices p 1).val * 120 + (leechSeventhE8A2Indices p 2).val

set_option maxHeartbeats 8000000 in
-- Check the 1119 adjacent pairs of the original sorted root-triple list.
/-- Consecutive original candidate keys are strictly increasing. -/
theorem leechSeventhE8A2PlaneKey_adjacent : ∀ i : Fin 1119,
    leechSeventhE8A2PlaneKey i.castSucc < leechSeventhE8A2PlaneKey i.succ := by
  decide +kernel

/-- The original candidate keys are strictly increasing throughout the finite catalogue. -/
theorem leechSeventhE8A2PlaneKey_strictMono : StrictMono leechSeventhE8A2PlaneKey :=
  Fin.strictMono_iff_lt_succ.mpr leechSeventhE8A2PlaneKey_adjacent

/-- Equality of all three original root-line addresses identifies the candidate. -/
theorem leechSeventhE8A2Indices_injective : Function.Injective leechSeventhE8A2Indices := by
  intro p q h
  apply leechSeventhE8A2PlaneKey_strictMono.injective
  simp only [leechSeventhE8A2PlaneKey, h]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
