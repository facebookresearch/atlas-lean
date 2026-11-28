/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.TriangleQueryResilienceDefs

namespace MetaMathlibExt.Complexity.NPComplete.TriangleQueryResilience

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open Cslib.Databases.ConjunctiveQueries

private theorem accepts_encoding (i : TriangleQueryResilienceInstance) :
    triangleQueryResilienceDec (bitEncode i) = true ↔
      WellFormed i ∧ TriangleQueryResilienceFeasible i := by
  simp [triangleQueryResilienceDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : triangleQueryResilienceDec [true] = false := by
  have h : bitDecode (α := TriangleQueryResilienceInstance) [true] = none := rfl
  simp [triangleQueryResilienceDec, h]

/-- The one-triangle database `R(0, 1), S(1, 2), T(2, 0)`. -/
private abbrev oneTriangle (k : ℕ) : TriangleQueryResilienceInstance :=
  ([(0, 1)], [(1, 2)], [(2, 0)], k)

/-- The identity assignment satisfies the triangle query on the one-triangle database. -/
private theorem oneTriangle_sat (k : ℕ) :
    Satisfies (database (oneTriangle k)) triangleQuery id := by
  simp [Satisfies, triangleQuery, database]

/-- Deleting the one `R` tuple destroys the only triangle, so one deletion suffices. -/
example : triangleQueryResilienceDec (bitEncode (oneTriangle 1)) = true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed; decide, ⟨id, oneTriangle_sat 1⟩,
    fun r => if r = 0 then ∅ else database (oneTriangle 1) r, ?_, ?_, ?_⟩
  · intro r
    dsimp only
    split_ifs <;> simp
  · simp [Finset.sum_range_succ, database]
  · rintro ⟨σ, hσ⟩
    have := hσ (0, [0, 1]) (by simp [triangleQuery])
    simp at this

/-- With no deletions allowed, the triangle survives. -/
example : triangleQueryResilienceDec (bitEncode (oneTriangle 0)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨-, -, D', -, hcard, hD'⟩
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hcard
  have hsub : ∀ r < 3, database (oneTriangle 0) r ⊆ D' r := by
    intro r hr
    rw [← Finset.sdiff_eq_empty_iff_subset, ← Finset.card_eq_zero]
    rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2) with rfl | rfl | rfl <;> omega
  refine hD' ⟨id, fun a ha => ?_⟩
  have hr : a.1 < 3 := by
    simp [triangleQuery] at ha
    rcases ha with rfl | rfl | rfl <;> simp
  exact hsub a.1 hr (oneTriangle_sat 0 a ha)

/-- The rejected instance is well formed, so the rejection comes from the deletion budget. -/
example : WellFormed (oneTriangle 0) := by
  unfold WellFormed
  decide

/-- `R(0, 1), S(1, 2), T(2, 1)` has no triangle, so it is rejected for every budget: the
language requires the query to hold before any deletion. -/
example :
    triangleQueryResilienceDec
      (bitEncode (([(0, 1)], [(1, 2)], [(2, 1)], 5) : TriangleQueryResilienceInstance)) =
        false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨-, ⟨σ, hσ⟩, -⟩
  simp [Satisfies, triangleQuery, database] at hσ
  omega

end MetaMathlibExt.Complexity.NPComplete.TriangleQueryResilience
