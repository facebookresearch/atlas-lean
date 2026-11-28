/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.TerrainGuardingDefs

namespace MetaMathlibExt.Complexity.NPComplete.TerrainGuarding

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : TerrainGuardingInstance) :
    terrainGuardingDec (bitEncode i) = true ↔ WellFormed i ∧ TerrainGuardingFeasible i := by
  simp [terrainGuardingDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : terrainGuardingDec [true] = false := by
  have h : bitDecode (α := TerrainGuardingInstance) [true] = none := rfl
  simp [terrainGuardingDec, h]

/-- The integer point `(x, y)` with `x, y ≥ 0`, as a pair of rational codes. -/
private abbrev pt (x y : ℕ) : RatCode × RatCode := (((x, 0), 1), ((y, 0), 1))

private theorem toPoint_pt (x y : ℕ) : toPoint (pt x y) = ((x : ℝ), (y : ℝ)) := by
  simp [toPoint, RatCode.val]

/-- On the flat terrain from `(0, 0)` to `(2, 0)`, the guard at `(0, 0)` sees `(2, 0)`. -/
example :
    terrainGuardingDec
      (bitEncode (([pt 0 0, pt 2 0], [pt 0 0], [pt 2 0], 1) : TerrainGuardingInstance)) =
        true := by
  apply (accepts_encoding _).2
  refine ⟨⟨?_, by simp, ?_, ?_, ?_, by simp, by simp⟩, Finset.univ, by simp, ?_⟩
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl <;> simp
  · simp [RatCode.val]
  · intro g hg
    simp at hg
    subst hg
    exact ⟨(pt 0 0, pt 2 0), by simp, left_mem_segment ℝ _ _⟩
  · intro p hp
    simp at hp
    subst hp
    exact ⟨(pt 0 0, pt 2 0), by simp, right_mem_segment ℝ _ _⟩
  · intro p hp
    simp at hp
    subst hp
    refine ⟨⟨0, by simp⟩, by simp, ?_⟩
    rintro z ⟨a, b, -, -, -, rfl⟩ t ⟨e, he, ht⟩ -
    simp at he
    subst he
    obtain ⟨a', b', -, -, -, rfl⟩ := ht
    simp [toPoint_pt]

/-- Raising the middle of the terrain to `(1, 1)` blocks the same guard: the segment from
`(0, 0)` to `(2, 0)` passes below the terrain point `(1, 1)`. -/
example :
    terrainGuardingDec
      (bitEncode (([pt 0 0, pt 1 1, pt 2 0], [pt 0 0], [pt 2 0], 1) :
        TerrainGuardingInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨-, S, -, hS⟩
  obtain ⟨g, -, hg⟩ := hS (pt 2 0) (by simp)
  have hg0 : g = ⟨0, by simp⟩ := Fin.ext (by have := g.isLt; simp at this ⊢)
  subst hg0
  have hz : ((1 : ℝ), (0 : ℝ)) ∈ segment ℝ (toPoint (pt 0 0)) (toPoint (pt 2 0)) := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    simp [toPoint_pt]
  have ht : ((1 : ℝ), (1 : ℝ)) ∈ terrain ([pt 0 0, pt 1 1, pt 2 0], [pt 0 0], [pt 2 0], 1) := by
    refine ⟨(pt 0 0, pt 1 1), by simp, ?_⟩
    simpa [toPoint_pt] using right_mem_segment ℝ (toPoint (pt 0 0)) (toPoint (pt 1 1))
  have := hg _ hz _ ht rfl
  norm_num at this

/-- The rejected instance is well formed, so the rejection comes from visibility. -/
example :
    WellFormed (([pt 0 0, pt 1 1, pt 2 0], [pt 0 0], [pt 2 0], 1) : TerrainGuardingInstance) := by
  refine ⟨?_, by simp, ?_, ?_, ?_, by simp, by simp⟩
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> simp
  · simp [RatCode.val]
  · intro g hg
    simp at hg
    subst hg
    exact ⟨(pt 0 0, pt 1 1), by simp, left_mem_segment ℝ _ _⟩
  · intro p hp
    simp at hp
    subst hp
    exact ⟨(pt 1 1, pt 2 0), by simp, right_mem_segment ℝ _ _⟩

end MetaMathlibExt.Complexity.NPComplete.TerrainGuarding
