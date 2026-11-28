/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.TwoDimensionalConsecutiveSetsSizeFiveDefs

namespace MetaMathlibExt.Complexity.NPComplete.TwoDimensionalConsecutiveSetsSizeFive

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open TwoDimensionalConsecutiveSets
  (TwoDimensionalConsecutiveSetsInstance TwoDimensionalConsecutiveSetsFeasible)

private theorem accepts_encoding (i : TwoDimensionalConsecutiveSetsInstance) :
    twoDimensionalConsecutiveSetsSizeFiveDec (bitEncode i) = true ↔
      WellFormed i ∧ TwoDimensionalConsecutiveSetsFeasible i := by
  simp [twoDimensionalConsecutiveSetsSizeFiveDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : twoDimensionalConsecutiveSetsSizeFiveDec [true] = false := by
  have h : bitDecode (α := TwoDimensionalConsecutiveSetsInstance) [true] = none := rfl
  simp [twoDimensionalConsecutiveSetsSizeFiveDec, h]

/-- Putting symbol `x` into the part `X_x` places `{0, 1}` in `X_0, X_1` and `{1, 2}` in
`X_1, X_2`. -/
example :
    twoDimensionalConsecutiveSetsSizeFiveDec
      (bitEncode ((3, [[0, 1], [1, 2]]) : TwoDimensionalConsecutiveSetsInstance)) = true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed TwoDimensionalConsecutiveSets.WellFormed; decide, id, ?_⟩
  intro S hS
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with rfl | rfl
  · exact ⟨by decide, 0, by decide⟩
  · exact ⟨by decide, 1, by decide⟩

/-- Each pair of `{0, 1, 2}` would need parts at distance exactly one, which no three
integers achieve. -/
example :
    twoDimensionalConsecutiveSetsSizeFiveDec
      (bitEncode ((3, [[0, 1], [1, 2], [0, 2]]) : TwoDimensionalConsecutiveSetsInstance)) =
        false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨g, hg⟩ := ((accepts_encoding _).1 h).2
  obtain ⟨h₀₁, l₀₁, hl₀₁⟩ := hg [0, 1] (by simp)
  obtain ⟨h₁₂, l₁₂, hl₁₂⟩ := hg [1, 2] (by simp)
  obtain ⟨h₀₂, l₀₂, hl₀₂⟩ := hg [0, 2] (by simp)
  have a₀₁ : g 0 ≠ g 1 := fun e => absurd (h₀₁ 0 (by simp) 1 (by simp) e) (by decide)
  have a₁₂ : g 1 ≠ g 2 := fun e => absurd (h₁₂ 1 (by simp) 2 (by simp) e) (by decide)
  have a₀₂ : g 0 ≠ g 2 := fun e => absurd (h₀₂ 0 (by simp) 2 (by simp) e) (by decide)
  have b₀ := hl₀₁ 0 (by simp)
  have b₁ := hl₀₁ 1 (by simp)
  have c₁ := hl₁₂ 1 (by simp)
  have c₂ := hl₁₂ 2 (by simp)
  have d₀ := hl₀₂ 0 (by simp)
  have d₂ := hl₀₂ 2 (by simp)
  simp only [List.length_cons, List.length_nil] at b₀ b₁ c₁ c₂ d₀ d₂
  omega

/-- A six-element subset is outside the size-five restriction. -/
example :
    twoDimensionalConsecutiveSetsSizeFiveDec
      (bitEncode ((6, [[0, 1, 2, 3, 4, 5]]) : TwoDimensionalConsecutiveSetsInstance)) =
        false := by
  rw [Bool.eq_false_iff]
  intro h
  have hw := ((accepts_encoding _).1 h).1.2 [0, 1, 2, 3, 4, 5] (by simp)
  revert hw
  decide

/-- The same six-element subset is feasible in the unrestricted problem. -/
example :
    TwoDimensionalConsecutiveSetsFeasible
      ((6, [[0, 1, 2, 3, 4, 5]]) : TwoDimensionalConsecutiveSetsInstance) := by
  refine ⟨id, ?_⟩
  intro S hS
  simp only [List.mem_singleton] at hS
  subst hS
  exact ⟨by decide, 0, by decide⟩

end MetaMathlibExt.Complexity.NPComplete.TwoDimensionalConsecutiveSetsSizeFive
