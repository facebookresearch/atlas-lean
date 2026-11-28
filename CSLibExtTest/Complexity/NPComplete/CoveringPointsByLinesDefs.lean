/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.CoveringPointsByLinesDefs
-- Membership in the line through two points as a `lineMap` value.
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
-- `linear_combination`, for the non-collinearity argument.
import Mathlib.Tactic.LinearCombination

namespace MetaMathlibExt.Complexity.NPComplete.CoveringPointsByLines

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open GeometricTravelingSalesman (point toInt)

/-- On an encoded instance the language is well-formedness and feasibility. -/
private theorem dec_bitEncode (i : CoveringPointsByLinesInstance) :
    coveringPointsByLinesDec (bitEncode i) = true ↔
      WellFormed i ∧ CoveringPointsByLinesFeasible i := by
  simp [coveringPointsByLinesDec, bitDecode_bitEncode]

/-- The points `(0, 0)`, `(1, 1)`, `(2, 2)` on the diagonal, with one line. -/
private abbrev diagonal : CoveringPointsByLinesInstance :=
  ([((0, 0), (0, 0)), ((1, 0), (1, 0)), ((2, 0), (2, 0))], 1)

/-- The corners `(0, 0)`, `(1, 0)`, `(0, 1)` of a right triangle, with `K` lines. -/
private abbrev corners (K : ℕ) : CoveringPointsByLinesInstance :=
  ([((0, 0), (0, 0)), ((1, 0), (0, 0)), ((0, 0), (1, 0))], K)

example : WellFormed diagonal := by unfold WellFormed; decide

example : WellFormed (corners 1) := by unfold WellFormed; decide

/-- The point `(x, y)` lies on the line through `a` and `b` when it is `lineMap a b r`. -/
private theorem mem_line_of_eq {a b p : ℝ × ℝ} (r : ℝ) (h : (1 - r) • a + r • b = p) :
    p ∈ line[ℝ, a, b] :=
  mem_affineSpan_pair_iff_exists_lineMap_eq.2 ⟨r, by rw [AffineMap.lineMap_apply_module, h]⟩

/-- Yes-instance: the line through `(0, 0)` and `(1, 1)` covers all three diagonal points. -/
example : coveringPointsByLinesDec (bitEncode diagonal) = true := by
  refine (dec_bitEncode _).2 ⟨by unfold WellFormed; decide, fun _ => ((0, 0), (1, 1)),
    fun _ => by simp, fun q hq => ⟨0, ?_⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact mem_line_of_eq 0 (by simp [point, toInt])
  · exact mem_line_of_eq 1 (by simp [point, toInt])
  · exact mem_line_of_eq 2 (by ext <;> simp [point, toInt])

/-- Two lines, through `(0, 0), (1, 0)` and through `(0, 0), (0, 1)`, cover the corners. -/
example : coveringPointsByLinesDec (bitEncode (corners 2)) = true := by
  refine (dec_bitEncode _).2 ⟨by unfold WellFormed; decide,
    fun j => if j = 0 then ((0, 0), (1, 0)) else ((0, 0), (0, 1)),
    fun j => by fin_cases j <;> simp, fun q hq => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨0, mem_line_of_eq 0 (by simp [point, toInt])⟩
  · exact ⟨0, mem_line_of_eq 1 (by simp [point, toInt])⟩
  · exact ⟨1, mem_line_of_eq 1 (by simp [point, toInt])⟩

/-- The coordinates of a point `lineMap a b r`. -/
private theorem coords_of_mem {a b p : ℝ × ℝ} (h : p ∈ line[ℝ, a, b]) :
    ∃ r : ℝ, (1 - r) * a.1 + r * b.1 = p.1 ∧ (1 - r) * a.2 + r * b.2 = p.2 := by
  obtain ⟨r, rfl⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.1 h
  exact ⟨r, by simp [AffineMap.lineMap_apply_module]⟩

/-- No line contains the three corners: they are not collinear. -/
private theorem corners_one_not_feasible : ¬ CoveringPointsByLinesFeasible (corners 1) := by
  rintro ⟨L, -, hcov⟩
  obtain ⟨j₁, h₁⟩ := hcov ((0, 0), (0, 0)) (by simp)
  obtain ⟨j₂, h₂⟩ := hcov ((1, 0), (0, 0)) (by simp)
  obtain ⟨j₃, h₃⟩ := hcov ((0, 0), (1, 0)) (by simp)
  obtain rfl := Subsingleton.elim j₁ 0
  obtain rfl := Subsingleton.elim j₂ 0
  obtain rfl := Subsingleton.elim j₃ 0
  obtain ⟨r₁, e₁, f₁⟩ := coords_of_mem h₁
  obtain ⟨r₂, e₂, f₂⟩ := coords_of_mem h₂
  obtain ⟨r₃, e₃, f₃⟩ := coords_of_mem h₃
  simp only [point, toInt, Prod.map] at e₁ f₁ e₂ f₂ e₃ f₃
  norm_num at e₁ f₁ e₂ f₂ e₃ f₃
  set a := (L 0).1
  set b := (L 0).2
  have : (1 : ℝ) = 0 := by
    linear_combination (-((r₃ - r₁) * (b.2 - a.2))) * (e₂ - e₁) - (f₃ - f₁) +
      ((r₃ - r₁) * (b.1 - a.1)) * (f₂ - f₁)
  exact one_ne_zero this

/-- No-instance: the corners are well formed but need two lines, not one. -/
example : coveringPointsByLinesDec (bitEncode (corners 1)) = false := by
  rw [Bool.eq_false_iff]
  exact fun h => corners_one_not_feasible ((dec_bitEncode _).1 h).2

/-- Malformed: a repeated point is rejected, although one line covers it. -/
example : coveringPointsByLinesDec
    (bitEncode (([((0, 0), (0, 0)), ((0, 0), (0, 0))], 1) : CoveringPointsByLinesInstance)) =
      false := by
  rw [Bool.eq_false_iff]
  intro h
  have := ((dec_bitEncode _).1 h).1
  revert this
  unfold WellFormed
  decide

/-- A lone continuation bit is a truncated instance encoding. -/
example : bitDecode (α := CoveringPointsByLinesInstance) [true] = none := rfl

/-- Undecodable: the language rejects the lone bit `[true]`. -/
example : coveringPointsByLinesDec [true] = false := rfl

end MetaMathlibExt.Complexity.NPComplete.CoveringPointsByLines
