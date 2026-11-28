/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.WeakRectangleVisibilityRecognitionDefs
import Mathlib.Tactic.Linarith

namespace MetaMathlibExt.Complexity.NPComplete.WeakRectangleVisibilityRecognition

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : WeakRectangleVisibilityInstance) :
    weakRectangleVisibilityRecognitionDec (bitEncode i) = true ↔
      WellFormed i ∧ WeakRectangleVisibilityFeasible i := by
  simp [weakRectangleVisibilityRecognitionDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : weakRectangleVisibilityRecognitionDec [true] = false := by
  have h : bitDecode (α := WeakRectangleVisibilityInstance) [true] = none := rfl
  simp [weakRectangleVisibilityRecognitionDec, h]

/-- The layout `[0, 1] × [0, 1]` for vertex `0` and `[2, 3] × [0, 1]` for vertex `1`. -/
private noncomputable def layout (v : Fin 2) : Rect := if v = 0 then (0, 1, 0, 1) else (2, 3, 0, 1)

private theorem vertices (v : Fin 2) : v = 0 ∨ v = 1 := by
  revert v
  decide

/-- The band `[1, 2] × [0, 1]` joins the right side of the first rectangle to the left side of
the second and meets no rectangle interior. -/
private theorem band : IsBandOfVisibility layout 0 1 (1, 2, 0, 1) := by
  refine ⟨by norm_num [Rect.NonDegenerate], ⟨0, ⟨1, ?_⟩, ⟨0, ?_⟩⟩, ?_⟩
  · intro p hp
    simpa [Rect.side, layout] using hp
  · intro p hp
    simpa [Rect.side, layout, oppositeSide] using hp
  · intro w
    rw [Set.disjoint_left]
    rintro p ⟨⟨h₁, h₂⟩, -⟩ ⟨⟨h₃, h₄⟩, -⟩
    rcases vertices w with rfl | rfl <;> simp [layout] at h₁ h₂ h₃ h₄ <;> linarith

/-- The same band, read from the second rectangle. -/
private theorem band' : IsBandOfVisibility layout 1 0 (1, 2, 0, 1) := by
  obtain ⟨hnd, -, hdisj⟩ := band
  refine ⟨hnd, ⟨1, ⟨0, ?_⟩, ⟨1, ?_⟩⟩, hdisj⟩
  · intro p hp
    simpa [Rect.side, layout] using hp
  · intro p hp
    simpa [Rect.side, layout, oppositeSide] using hp

/-- A single edge is a weak rectangle visibility graph: two unit squares side by side see each
other through the band between them. -/
example :
    weakRectangleVisibilityRecognitionDec
      (bitEncode ((2, [(0, 1)]) : WeakRectangleVisibilityInstance)) = true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed; decide, layout, ⟨?_, ?_⟩, ?_⟩
  · intro v
    rcases vertices v with rfl | rfl <;> norm_num [Rect.NonDegenerate, layout]
  · intro u v huv
    rw [Set.disjoint_left]
    rintro p ⟨⟨h₁, h₂⟩, -⟩ ⟨⟨h₃, h₄⟩, -⟩
    rcases vertices u with rfl | rfl <;> rcases vertices v with rfl | rfl <;>
      simp [layout] at huv h₁ h₂ h₃ h₄ <;> linarith
  · intro u v h
    rcases vertices u with rfl | rfl <;> rcases vertices v with rfl | rfl
    · exact absurd h (SimpleGraph.irrefl _)
    · exact ⟨_, band⟩
    · exact ⟨_, band'⟩
    · exact absurd h (SimpleGraph.irrefl _)

/-- Listing the same edge in both orientations is rejected as a malformed edge list, although
the graph it denotes is the accepted single edge. -/
example :
    weakRectangleVisibilityRecognitionDec
      (bitEncode ((2, [(0, 1), (1, 0)]) : WeakRectangleVisibilityInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨hwf, -⟩
  revert hwf
  unfold WellFormed
  decide

end MetaMathlibExt.Complexity.NPComplete.WeakRectangleVisibilityRecognition
