/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.LineArrangement
import Mathlib.Tactic.NormNum

open Projectivization
open scoped LinearAlgebra.Projectivization

/-! ### Two lines meet in their cross product -/

/-- The points on two distinct lines are exactly their cross product. -/
example (p ℓ ℓ' : ℙ ℚ (Fin 3 → ℚ)) (h : ℓ ≠ ℓ') :
    p = cross ℓ ℓ' ↔ p.orthogonal ℓ ∧ p.orthogonal ℓ' :=
  eq_cross_iff h

/-! ### A pencil of two lines -/

private theorem e₀_ne_zero : (![1, 0, 0] : Fin 3 → ℚ) ≠ 0 := by
  intro h
  simpa using congrFun h 0

private theorem e₁_ne_zero : (![0, 1, 0] : Fin 3 → ℚ) ≠ 0 := by
  intro h
  simpa using congrFun h 1

private theorem e₂_ne_zero : (![0, 0, 1] : Fin 3 → ℚ) ≠ 0 := by
  intro h
  simpa using congrFun h 2

/-- The line `x₀ = 0`. -/
private noncomputable def ℓ₀ : ℙ ℚ (Fin 3 → ℚ) := mk ℚ ![1, 0, 0] e₀_ne_zero

/-- The line `x₁ = 0`. -/
private noncomputable def ℓ₁ : ℙ ℚ (Fin 3 → ℚ) := mk ℚ ![0, 1, 0] e₁_ne_zero

/-- The point `[0 : 0 : 1]`. -/
private noncomputable def p₂ : ℙ ℚ (Fin 3 → ℚ) := mk ℚ ![0, 0, 1] e₂_ne_zero

private theorem ℓ₀_ne_ℓ₁ : ℓ₀ ≠ ℓ₁ := by
  intro h
  obtain ⟨a, ha⟩ := (mk_eq_mk_iff' ℚ _ _ e₀_ne_zero e₁_ne_zero).1 h
  simpa using congrFun ha 0

private theorem p₂_orthogonal_ℓ₀ : p₂.orthogonal ℓ₀ := by
  rw [p₂, ℓ₀, orthogonal_mk]
  simp [dotProduct, Fin.sum_univ_three]

private theorem p₂_orthogonal_ℓ₁ : p₂.orthogonal ℓ₁ := by
  rw [p₂, ℓ₁, orthogonal_mk]
  simp [dotProduct, Fin.sum_univ_three]

open Classical in
/-- The arrangement of the two lines `x₀ = 0` and `x₁ = 0`. -/
private noncomputable def pencil : LineArrangement ℚ :=
  ⟨{ℓ₀, ℓ₁}, (Finset.card_pair ℓ₀_ne_ℓ₁).ge⟩

/-- The two lines meet at `[0 : 0 : 1]`, which therefore has multiplicity two. -/
example : p₂ ∈ pencil.singularPoints := by
  rw [LineArrangement.mem_singularPoints_iff_exists]
  exact ⟨ℓ₀, by simp [pencil], ℓ₁, by simp [pencil], ℓ₀_ne_ℓ₁, p₂_orthogonal_ℓ₀, p₂_orthogonal_ℓ₁⟩

private theorem pencil_multiplicity_p₂ : pencil.multiplicity p₂ = 2 := by
  refine le_antisymm ?_ ?_
  · calc pencil.multiplicity p₂ ≤ pencil.lines.card := pencil.multiplicity_le_card p₂
      _ = 2 := by classical exact Finset.card_pair ℓ₀_ne_ℓ₁
  · rw [← LineArrangement.mem_singularPoints_iff, LineArrangement.mem_singularPoints_iff_exists]
    exact ⟨ℓ₀, by simp [pencil], ℓ₁, by simp [pencil], ℓ₀_ne_ℓ₁, p₂_orthogonal_ℓ₀,
      p₂_orthogonal_ℓ₁⟩

/-- `[0 : 0 : 1]` is the only singular point: a point on both lines is their intersection. -/
private theorem pencil_singularPoints : pencil.singularPoints = {p₂} := by
  ext q
  rw [Finset.mem_singleton, LineArrangement.mem_singularPoints_iff_exists]
  constructor
  · rintro ⟨ℓ, hℓ, ℓ', hℓ', hne, hq, hq'⟩
    classical
    simp only [pencil, Finset.mem_insert, Finset.mem_singleton] at hℓ hℓ'
    have hboth : q.orthogonal ℓ₀ ∧ q.orthogonal ℓ₁ := by
      rcases hℓ with rfl | rfl <;> rcases hℓ' with rfl | rfl
      · exact absurd rfl hne
      · exact ⟨hq, hq'⟩
      · exact ⟨hq', hq⟩
      · exact absurd rfl hne
    exact ((eq_cross_iff ℓ₀_ne_ℓ₁).2 hboth).trans
      ((eq_cross_iff ℓ₀_ne_ℓ₁).2 ⟨p₂_orthogonal_ℓ₀, p₂_orthogonal_ℓ₁⟩).symm
  · rintro rfl
    exact ⟨ℓ₀, by simp [pencil], ℓ₁, by simp [pencil], ℓ₀_ne_ℓ₁, p₂_orthogonal_ℓ₀,
      p₂_orthogonal_ℓ₁⟩

/-- A pencil of two lines has Harbourne constant `(2² - 2²) / 1 = 0`. -/
example : pencil.hConstant = 0 := by
  classical
  rw [LineArrangement.hConstant, pencil_singularPoints, Finset.sum_singleton,
    pencil_multiplicity_p₂, show pencil.lines.card = 2 from Finset.card_pair ℓ₀_ne_ℓ₁]
  norm_num

/-- Arrangements are determined by their lines. -/
example (A B : LineArrangement ℚ) (h : A.lines = B.lines) : A = B :=
  LineArrangement.ext h

/-- Every arrangement has a singular point, so the H-constant has a positive denominator. -/
example (A : LineArrangement ℚ) : 0 < A.singularPoints.card :=
  A.card_singularPoints_pos
